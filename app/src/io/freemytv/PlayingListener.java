package io.freemytv;

import android.content.ComponentName;
import android.content.Context;
import android.graphics.Bitmap;
import android.media.MediaMetadata;
import android.media.session.MediaController;
import android.media.session.MediaSessionManager;
import android.media.session.PlaybackState;
import android.os.Handler;
import android.os.Looper;
import android.service.notification.NotificationListenerService;

import org.json.JSONArray;
import org.json.JSONObject;

import java.io.File;
import java.io.FileOutputStream;
import java.nio.charset.StandardCharsets;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * What the apps play, while they play it (the title, where you are, the length and, when the app gives one, its
 * picture), for the home screen's Continue row. Android hands the playing apps' media sessions to a notification
 * listener; the notifications themselves are never read. On only in Free My TV mode (HomeMode turns the access on
 * and off over ADB); its own small process. What it saw goes to playing.json, which Recs reads in the home screen.
 */
public final class PlayingListener extends NotificationListenerService {
    static final String FILE = "playing.json";
    private static final int MAX = 20;
    private static final long WRITE_EVERY_MS = 30_000;

    private final Handler handler = new Handler(Looper.getMainLooper());
    private final Map<MediaController.Callback, MediaController> watching = new HashMap<>();
    private MediaSessionManager sessions;
    private final MediaSessionManager.OnActiveSessionsChangedListener changed = this::follow;
    private final Map<String, Long> writtenAt = new HashMap<>();

    @Override public void onListenerConnected() {
        sessions = (MediaSessionManager) getSystemService(Context.MEDIA_SESSION_SERVICE);
        if (sessions == null) return;
        ComponentName me = new ComponentName(this, PlayingListener.class);
        try {
            sessions.addOnActiveSessionsChangedListener(changed, me, handler);
            follow(sessions.getActiveSessions(me));
        } catch (SecurityException e) {
            AppLog.w("playing: " + e.getMessage());
        }
    }

    @Override public void onListenerDisconnected() {
        if (sessions != null) sessions.removeOnActiveSessionsChangedListener(changed);
        for (Map.Entry<MediaController.Callback, MediaController> e : watching.entrySet()) e.getValue().unregisterCallback(e.getKey());
        watching.clear();
    }

    private void follow(List<MediaController> list) {
        if (list == null) return;
        for (final MediaController mc : list) {
            if (watching.containsValue(mc) || mc.getPackageName().equals(getPackageName())) continue;
            MediaController.Callback cb = new MediaController.Callback() {
                @Override public void onPlaybackStateChanged(PlaybackState state) { seen(mc, false); }
                @Override public void onMetadataChanged(MediaMetadata metadata) { seen(mc, true); }
                @Override public void onSessionDestroyed() {
                    seen(mc, true);
                    mc.unregisterCallback(this);
                    watching.remove(this);
                }
            };
            mc.registerCallback(cb, handler);
            watching.put(cb, mc);
            seen(mc, true);
        }
    }

    /** Playing (or paused past the start): saved, at most every 30 s per title unless the title just changed. */
    private void seen(MediaController mc, boolean now) {
        PlaybackState state = mc.getPlaybackState();
        MediaMetadata md = mc.getMetadata();
        if (state == null || md == null) return;
        int s = state.getState();
        if (s != PlaybackState.STATE_PLAYING && s != PlaybackState.STATE_PAUSED) return;
        String pkg = mc.getPackageName();
        if (HomeApps.launchIntent(getPackageManager(), pkg) == null) return;   // the system's own players
        CharSequence t = md.getDescription() == null ? null : md.getDescription().getTitle();
        if (t == null) t = md.getText(MediaMetadata.METADATA_KEY_TITLE);
        String title = t == null ? "" : t.toString().trim();
        if (title.isEmpty() || state.getPosition() <= 0) return;
        String key = pkg + "|" + title;
        long at = System.currentTimeMillis();
        Long last = writtenAt.get(key);
        if (!now && last != null && at - last < WRITE_EVERY_MS) return;
        writtenAt.put(key, at);
        long duration = md.getLong(MediaMetadata.METADATA_KEY_DURATION);
        Bitmap art = md.getBitmap(MediaMetadata.METADATA_KEY_ART);
        if (art == null) art = md.getBitmap(MediaMetadata.METADATA_KEY_DISPLAY_ICON);
        if (art == null) art = md.getBitmap(MediaMetadata.METADATA_KEY_ALBUM_ART);
        save(this, pkg, title, state.getPosition(), duration, art, at);
    }

    private static synchronized void save(Context c, String pkg, String title, long position, long duration, Bitmap art, long at) {
        try {
            JSONArray old = read(c), out = new JSONArray();
            String artPath = "";
            File dir = new File(c.getFilesDir(), "playing");
            String name = Integer.toHexString((pkg + "|" + title).hashCode()) + ".jpg";
            File artFile = new File(dir, name);
            if (art != null && !artFile.exists()) {
                //noinspection ResultOfMethodCallIgnored
                dir.mkdirs();
                Bitmap small = art.getWidth() > 480 ? Ui.downscale(art, 480, Math.max(1, 480 * art.getHeight() / art.getWidth())) : art;
                try (FileOutputStream f = new FileOutputStream(artFile)) {
                    small.compress(Bitmap.CompressFormat.JPEG, 85, f);
                }
            }
            if (artFile.exists()) artPath = artFile.getPath();
            out.put(new JSONObject().put("pkg", pkg).put("title", title).put("position", position).put("duration", duration)
                    .put("art", artPath).put("at", at));
            for (int i = 0; i < old.length() && out.length() < MAX; i++) {
                JSONObject o = old.optJSONObject(i);
                if (o != null && !(pkg.equals(o.optString("pkg")) && title.equals(o.optString("title")))) out.put(o);
            }
            File tmp = new File(c.getFilesDir(), FILE + ".tmp");
            try (FileOutputStream f = new FileOutputStream(tmp)) {
                f.write(out.toString().getBytes(StandardCharsets.UTF_8));
            }
            //noinspection ResultOfMethodCallIgnored
            tmp.renameTo(new File(c.getFilesDir(), FILE));
        } catch (Exception e) {
            AppLog.w("playing: " + e.getMessage());
        }
    }

    /** What was seen playing, the last one first. */
    static JSONArray read(Context c) {
        File f = new File(c.getFilesDir(), FILE);
        if (!f.exists()) return new JSONArray();
        try (java.io.FileInputStream in = new java.io.FileInputStream(f)) {
            byte[] data = new byte[(int) f.length()];
            int n = 0;
            while (n < data.length) {
                int r = in.read(data, n, data.length - n);
                if (r < 0) break;
                n += r;
            }
            return new JSONArray(new String(data, 0, n, StandardCharsets.UTF_8));
        } catch (Exception e) {
            return new JSONArray();
        }
    }
}
