/* 
 * Copyright (C) 2008 Red Hat, Inc
 *
 * This library is free software; you can redistribute it and/or
 * modify it under the terms of the GNU Lesser General Public
 * License as published by the Free Software Foundation; either
 * version 2.1 of the License, or (at your option) any later version.
 *
 * This library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
 * Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General
 * Public License along with this library; if not, see <http://www.gnu.org/licenses/>.
 * 
 * Author: Matthias Clasen
 */

#include <locale.h>

#include <glib/glib.h>
#include <glib/gstdio.h>
#include <gio/gio.h>
#include <gio/gdesktopappinfo.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static GAppInfo *
create_app_info (const char *name)
{
  GError *error;
  GAppInfo *info;

  error = NULL;
  info = g_app_info_create_from_commandline ("true blah",
                                             name,
                                             G_APP_INFO_CREATE_NONE,
                                             &error);
  g_assert_no_error (error);

  /* this is necessary to ensure that the info is saved */
  g_app_info_set_as_default_for_type (info, "application/x-blah", &error);
  g_assert_no_error (error);
  g_app_info_remove_supports_type (info, "application/x-blah", &error);
  g_assert_no_error (error);
  g_app_info_reset_type_associations ("application/x-blah");
  
  return info;
}

static void
test_delete (void)
{
  GAppInfo *info;

  const char *id;
  char *filename;
  gboolean res;

  info = create_app_info ("Blah");
 
  id = g_app_info_get_id (info);
  g_assert_nonnull (id);

  filename = g_build_filename (g_get_user_data_dir (), "applications", id, NULL);

  res = g_file_test (filename, G_FILE_TEST_EXISTS);
  g_assert_true (res);

  res = g_app_info_can_delete (info);
  g_assert_true (res);

  res = g_app_info_delete (info);
  g_assert_true (res);

  res = g_file_test (filename, G_FILE_TEST_EXISTS);
  g_assert_false (res);

  g_object_unref (info);

  if (g_file_test ("/usr/share/applications/gedit.desktop", G_FILE_TEST_EXISTS))
    {
      info = (GAppInfo*)g_desktop_app_info_new_from_filename ("/usr/share/applications/gedit.desktop");
      g_assert_nonnull (info);
     
      res = g_app_info_can_delete (info);
      g_assert_false (res);
 
      res = g_app_info_delete (info);
      g_assert_false (res);
    }

  g_free (filename);
}

static void
test_default (void)
{
  GAppInfo *info, *info1, *info2, *info3;
  GList *list;
  GError *error = NULL;  

  info1 = create_app_info ("Blah1");
  info2 = create_app_info ("Blah2");
  info3 = create_app_info ("Blah3");

  g_app_info_set_as_default_for_type (info1, "application/x-test", &error);
  g_assert_no_error (error);

  g_app_info_set_as_default_for_type (info2, "application/x-test", &error);
  g_assert_no_error (error);

  info = g_app_info_get_default_for_type ("application/x-test", FALSE);
  g_assert_nonnull (info);
  g_assert_cmpstr (g_app_info_get_id (info), ==, g_app_info_get_id (info2));
  g_object_unref (info);

  /* now try adding something, but not setting as default */
  g_app_info_add_supports_type (info3, "application/x-test", &error);
  g_assert_no_error (error);

  /* check that info2 is still default */
  info = g_app_info_get_default_for_type ("application/x-test", FALSE);
  g_assert_nonnull (info);
  g_assert_cmpstr (g_app_info_get_id (info), ==, g_app_info_get_id (info2));
  g_object_unref (info);

  /* now remove info1 again */
  g_app_info_remove_supports_type (info1, "application/x-test", &error);
  g_assert_no_error (error);

  /* and make sure info2 is still default */
  info = g_app_info_get_default_for_type ("application/x-test", FALSE);
  g_assert_nonnull (info);
  g_assert_cmpstr (g_app_info_get_id (info), ==, g_app_info_get_id (info2));
  g_object_unref (info);

  /* now clean it all up */
  g_app_info_reset_type_associations ("application/x-test");

  list = g_app_info_get_all_for_type ("application/x-test");
  g_assert_null (list);

  g_app_info_delete (info1);
  g_app_info_delete (info2);
  g_app_info_delete (info3);

  g_object_unref (info1);
  g_object_unref (info2);
  g_object_unref (info3);
}

static void
test_fallback (void)
{
  GAppInfo *info1, *info2, *app = NULL;
  GList *apps, *recomm, *fallback, *list, *l, *m;
  GError *error = NULL;
  gint old_length;

  info1 = create_app_info ("Test1");
  info2 = create_app_info ("Test2");

  g_assert_true (g_content_type_is_a ("text/x-python", "text/plain"));

  apps = g_app_info_get_all_for_type ("text/x-python");
  old_length = g_list_length (apps);
  g_list_free_full (apps, g_object_unref);

  g_app_info_add_supports_type (info1, "text/x-python", &error);
  g_assert_no_error (error);

  g_app_info_add_supports_type (info2, "text/plain", &error);
  g_assert_no_error (error);

  /* check that both apps are registered */
  apps = g_app_info_get_all_for_type ("text/x-python");
  g_assert_cmpint (g_list_length (apps), ==, old_length + 2);

  /* check that Test1 is among the recommended apps */
  recomm = g_app_info_get_recommended_for_type ("text/x-python");
  g_assert_nonnull (recomm);
  for (l = recomm; l; l = l->next)
    {
      app = l->data;
      if (g_app_info_equal (info1, app))
        break;
    }
  g_assert_nonnull (app);
  g_assert_true (g_app_info_equal (info1, app));

  /* and that Test2 is among the fallback apps */
  fallback = g_app_info_get_fallback_for_type ("text/x-python");
  g_assert_nonnull (fallback);
  for (l = fallback; l; l = l->next)
    {
      app = l->data;
      if (g_app_info_equal (info2, app))
        break;
    }
  g_assert_cmpstr (g_app_info_get_name (app), ==, "Test2");

  /* check that recomm + fallback = all applications */
  list = g_list_concat (g_list_copy (recomm), g_list_copy (fallback));
  g_assert_cmpuint (g_list_length (list), ==, g_list_length (apps));

  for (l = list, m = apps; l != NULL && m != NULL; l = l->next, m = m->next)
    {
      g_assert_true (g_app_info_equal (l->data, m->data));
    }

  g_list_free (list);

  g_list_free_full (apps, g_object_unref);
  g_list_free_full (recomm, g_object_unref);
  g_list_free_full (fallback, g_object_unref);

  g_app_info_reset_type_associations ("text/x-python");
  g_app_info_reset_type_associations ("text/plain");

  g_app_info_delete (info1);
  g_app_info_delete (info2);

  g_object_unref (info1);
  g_object_unref (info2);
}

static void
test_last_used (void)
{
  GList *applications;
  GAppInfo *info1, *info2, *default_app;
  GError *error = NULL;

  info1 = create_app_info ("Test1");
  info2 = create_app_info ("Test2");

  g_app_info_set_as_default_for_type (info1, "application/x-test", &error);
  g_assert_no_error (error);

  g_app_info_add_supports_type (info2, "application/x-test", &error);
  g_assert_no_error (error);

  applications = g_app_info_get_recommended_for_type ("application/x-test");
  g_assert_cmpuint (g_list_length (applications), ==, 2);

  /* the first should be the default app now */
  g_assert_true (g_app_info_equal (g_list_nth_data (applications, 0), info1));
  g_assert_true (g_app_info_equal (g_list_nth_data (applications, 1), info2));

  g_list_free_full (applications, g_object_unref);

  g_app_info_set_as_last_used_for_type (info2, "application/x-test", &error);
  g_assert_no_error (error);

  applications = g_app_info_get_recommended_for_type ("application/x-test");
  g_assert_cmpuint (g_list_length (applications), ==, 2);

  default_app = g_app_info_get_default_for_type ("application/x-test", FALSE);
  g_assert_true (g_app_info_equal (default_app, info1));

  /* the first should be the other app now */
  g_assert_true (g_app_info_equal (g_list_nth_data (applications, 0), info2));
  g_assert_true (g_app_info_equal (g_list_nth_data (applications, 1), info1));

  g_list_free_full (applications, g_object_unref);

  g_app_info_reset_type_associations ("application/x-test");

  g_app_info_delete (info1);
  g_app_info_delete (info2);

  g_object_unref (info1);
  g_object_unref (info2);
  g_object_unref (default_app);
}

static void
test_extra_getters (void)
{
  GDesktopAppInfo *appinfo;
  const gchar *lang;
  gchar *s;
  gboolean b;

  lang = setlocale (LC_ALL, NULL);
  g_setenv ("LANGUAGE", "de_DE.UTF8", TRUE);
  setlocale (LC_ALL, "");

  appinfo = g_desktop_app_info_new_from_filename (g_test_get_filename (G_TEST_DIST, "appinfo-test-static.desktop", NULL));
  g_assert_nonnull (appinfo);

  g_assert_true (g_desktop_app_info_has_key (appinfo, "Terminal"));
  g_assert_false (g_desktop_app_info_has_key (appinfo, "Bratwurst"));

  s = g_desktop_app_info_get_string (appinfo, "StartupWMClass");
  g_assert_cmpstr (s, ==, "appinfo-class");
  g_free (s);

  s = g_desktop_app_info_get_locale_string (appinfo, "X-JunkFood");
  g_assert_cmpstr (s, ==, "Bratwurst");
  g_free (s);

  g_setenv ("LANGUAGE", "sv_SE.UTF8", TRUE);
  setlocale (LC_ALL, "");

  s = g_desktop_app_info_get_locale_string (appinfo, "X-JunkFood");
  g_assert_cmpstr (s, ==, "Burger"); /* fallback */
  g_free (s);

  b = g_desktop_app_info_get_boolean (appinfo, "Terminal");
  g_assert_true (b);

  g_object_unref (appinfo);

  g_setenv ("LANGUAGE", lang, TRUE);
  setlocale (LC_ALL, "");
}

static void
wait_for_file (const gchar *want_this,
               const gchar *but_not_this,
               const gchar *or_this)
{
  guint retries = 600;

  /* I hate time-based conditions in tests, but this will wait up to one
   * whole minute for "touch file" to finish running.  I think it should
   * be OK.
   *
   * 600 * 100ms = 60 seconds.
   */
  while (access (want_this, F_OK) != 0)
    {
      g_usleep (100000); /* 100ms */
      g_assert_cmpuint (retries, >, 0);
      retries--;
    }

  g_assert_cmpuint (access (but_not_this, F_OK), !=, 0);
  g_assert_cmpuint (access (or_this, F_OK), !=, 0);

  unlink (want_this);
  unlink (but_not_this);
  unlink (or_this);
}

static void
test_actions (void)
{
  const char *expected[] = { "frob", "tweak", "twiddle", "broken", NULL };
  const gchar * const *actions;
  GDesktopAppInfo *appinfo;
  gchar *name;

  appinfo = g_desktop_app_info_new_from_filename (g_test_get_filename (G_TEST_DIST, "appinfo-test-actions.desktop", NULL));
  g_assert_nonnull (appinfo);

  actions = g_desktop_app_info_list_actions (appinfo);
  g_assert_cmpstrv (actions, expected);

  name = g_desktop_app_info_get_action_name (appinfo, "frob");
  g_assert_cmpstr (name, ==, "Frobnicate");
  g_free (name);

  name = g_desktop_app_info_get_action_name (appinfo, "tweak");
  g_assert_cmpstr (name, ==, "Tweak");
  g_free (name);

  name = g_desktop_app_info_get_action_name (appinfo, "twiddle");
  g_assert_cmpstr (name, ==, "Twiddle");
  g_free (name);

  name = g_desktop_app_info_get_action_name (appinfo, "broken");
  g_assert_nonnull (name);
  g_assert_true (g_utf8_validate (name, -1, NULL));
  g_free (name);

  unlink ("frob"); unlink ("tweak"); unlink ("twiddle");

  g_desktop_app_info_launch_action (appinfo, "frob", NULL);
  wait_for_file ("frob", "tweak", "twiddle");

  g_desktop_app_info_launch_action (appinfo, "tweak", NULL);
  wait_for_file ("tweak", "frob", "twiddle");

  g_desktop_app_info_launch_action (appinfo, "twiddle", NULL);
  wait_for_file ("twiddle", "frob", "tweak");

  g_object_unref (appinfo);
}

static gchar *
run_apps (const gchar *command,
          const gchar *arg,
          gboolean     with_usr,
          gboolean     with_home,
          const gchar *locale_name,
          const gchar *language,
          const gchar *xdg_current_desktop)
{
  gboolean success;
  gchar **envp;
  gchar **argv;
  gint status;
  gchar *out;
  gchar *argv_str = NULL;

  argv = g_new (gchar *, 4);
  argv[0] = g_test_build_filename (G_TEST_BUILT, "apps", NULL);
  argv[1] = g_strdup (command);
  argv[2] = g_strdup (arg);
  argv[3] = NULL;

  envp = g_get_environ ();

  if (with_usr)
    {
      gchar *tmp = g_test_build_filename (G_TEST_DIST, "desktop-files", "usr", NULL);
      envp = g_environ_setenv (envp, "XDG_DATA_DIRS", tmp, TRUE);
      g_free (tmp);
    }
  else
    envp = g_environ_setenv (envp, "XDG_DATA_DIRS", "/does-not-exist", TRUE);

  if (with_home)
    {
      gchar *tmp = g_test_build_filename (G_TEST_DIST, "desktop-files", "home", NULL);
      envp = g_environ_setenv (envp, "XDG_DATA_HOME", tmp, TRUE);
      g_free (tmp);
    }
  else
    envp = g_environ_setenv (envp, "XDG_DATA_HOME", "/does-not-exist", TRUE);

  if (locale_name)
    envp = g_environ_setenv (envp, "LC_ALL", locale_name, TRUE);
  else
    envp = g_environ_setenv (envp, "LC_ALL", "C", TRUE);

  if (language)
    envp = g_environ_setenv (envp, "LANGUAGE", language, TRUE);
  else
    envp = g_environ_unsetenv (envp, "LANGUAGE");

  if (xdg_current_desktop)
    envp = g_environ_setenv (envp, "XDG_CURRENT_DESKTOP", xdg_current_desktop, TRUE);
  else
    envp = g_environ_unsetenv (envp, "XDG_CURRENT_DESKTOP");

  envp = g_environ_setenv (envp, "G_MESSAGES_DEBUG", "", TRUE);

  success = g_spawn_sync (NULL, argv, envp, 0, NULL, NULL, &out, NULL, &status, NULL);
  g_assert_true (success);
  g_assert_cmpuint (status, ==, 0);

  argv_str = g_strjoinv (" ", argv);
  g_test_message ("%s: `%s` returned: %s", G_STRFUNC, argv_str, out);
  g_free (argv_str);

  g_strfreev (envp);
  g_strfreev (argv);

  return out;
}

static void
assert_strings_equivalent (const gchar *expected,
                           const gchar *result)
{
  gchar **expected_words;
  gchar **result_words;
  gint i, j;

  expected_words = g_strsplit (expected, " ", 0);
  result_words = g_strsplit_set (result, " \n", 0);

  for (i = 0; expected_words[i]; i++)
    {
      for (j = 0; result_words[j]; j++)
        if (g_str_equal (expected_words[i], result_words[j]))
          goto got_it;

      g_test_fail_printf ("Unable to find expected string '%s' in result '%s'", expected_words[i], result);

got_it:
      continue;
    }

  g_assert_cmpint (g_strv_length (expected_words), ==, g_strv_length (result_words));
  g_strfreev (expected_words);
  g_strfreev (result_words);
}

static void
assert_list (const gchar *expected,
             gboolean     with_usr,
             gboolean     with_home,
             const gchar *locale_name,
             const gchar *language)
{
  gchar *result;

  result = run_apps ("list", NULL, with_usr, with_home, locale_name, language, NULL);
  g_strchomp (result);
  assert_strings_equivalent (expected, result);
  g_free (result);
}

static void
assert_info (const gchar *desktop_id,
             const gchar *expected,
             gboolean     with_usr,
             gboolean     with_home,
             const gchar *locale_name,
             const gchar *language)
{
  gchar *result;

  result = run_apps ("show-info", desktop_id, with_usr, with_home, locale_name, language, NULL);
  g_assert_cmpstr (result, ==, expected);
  g_free (result);
}

static void
assert_search (const gchar *search_string,
               const gchar *expected,
               gboolean     with_usr,
               gboolean     with_home,
               const gchar *locale_name,
               const gchar *language)
{
  gchar **expected_lines;
  gchar **result_lines;
  gchar *result;
  gint i;

  expected_lines = g_strsplit (expected, "\n", -1);
  result = run_apps ("search", search_string, with_usr, with_home, locale_name, language, NULL);
  result_lines = g_strsplit (result, "\n", -1);
  g_assert_cmpint (g_strv_length (expected_lines), ==, g_strv_length (result_lines));
  for (i = 0; expected_lines[i]; i++)
    assert_strings_equivalent (expected_lines[i], result_lines[i]);
  g_strfreev (expected_lines);
  g_strfreev (result_lines);
  g_free (result);
}

static void
assert_implementations (const gchar *interface,
                        const gchar *expected,
                        gboolean     with_usr,
                        gboolean     with_home)
{
  gchar *result;

  result = run_apps ("implementations", interface, with_usr, with_home, NULL, NULL, NULL);
  g_strchomp (result);
  assert_strings_equivalent (expected, result);
  g_free (result);
}

#define ALL_USR_APPS  "evince-previewer.desktop nautilus-classic.desktop gnome-font-viewer.desktop "         \
                      "baobab.desktop yelp.desktop eog.desktop cheese.desktop org.gnome.clocks.desktop "         \
                      "gnome-contacts.desktop kde4-kate.desktop gcr-prompter.desktop totem.desktop "         \
                      "gnome-terminal.desktop nautilus-autorun-software.desktop gcr-viewer.desktop "         \
                      "nautilus-connect-server.desktop kde4-dolphin.desktop gnome-music.desktop "            \
                      "kde4-konqbrowser.desktop gucharmap.desktop kde4-okular.desktop nautilus.desktop "     \
                      "gedit.desktop evince.desktop file-roller.desktop dconf-editor.desktop glade.desktop " \
                      "invalid-desktop.desktop"
#define HOME_APPS     "epiphany-weather-for-toronto-island-9c6a4e022b17686306243dada811d550d25eb1fb.desktop"
#define ALL_HOME_APPS HOME_APPS " eog.desktop"

static void
test_search (void)
{
  assert_list ("", FALSE, FALSE, NULL, NULL);
  assert_list (ALL_USR_APPS, TRUE, FALSE, NULL, NULL);
  assert_list (ALL_HOME_APPS, FALSE, TRUE, NULL, NULL);
  assert_list (ALL_USR_APPS " " HOME_APPS, TRUE, TRUE, NULL, NULL);

  /* The user has "installed" their own version of eog.desktop which
   * calls it "Eye of GNOME".  Do some testing based on that.
   *
   * We should always find "Pictures" keyword no matter where we look.
   */
  assert_search ("Picture", "eog.desktop\n", TRUE, TRUE, NULL, NULL);
  assert_search ("Picture", "eog.desktop\n", TRUE, FALSE, NULL, NULL);
  assert_search ("Picture", "eog.desktop\n", FALSE, TRUE, NULL, NULL);
  assert_search ("Picture", "", FALSE, FALSE, NULL, NULL);

  /* We should only find it called "eye of gnome" when using the user's
   * directory.
   */
  assert_search ("eye gnome", "", TRUE, FALSE, NULL, NULL);
  assert_search ("eye gnome", "eog.desktop\n", FALSE, TRUE, NULL, NULL);
  assert_search ("eye gnome", "eog.desktop\n", TRUE, TRUE, NULL, NULL);

  /* We should only find it called "image viewer" when _not_ using the
   * user's directory.
   */
  assert_search ("image viewer", "eog.desktop\n", TRUE, FALSE, NULL, NULL);
  assert_search ("image viewer", "", FALSE, TRUE, NULL, NULL);
  assert_search ("image viewer", "", TRUE, TRUE, NULL, NULL);

  /* There're "flatpak" apps (clocks) installed as well - they should *not*
   * match the prefix command ("/bin/sh") in the Exec= line though.
   */
  assert_search ("sh", "gnome-terminal.desktop\n", TRUE, FALSE, NULL, NULL);

  /* "frobnicator.desktop" is ignored by get_all() because the binary is
   * missing, but search should still find it (to avoid either stale results
   * from the cache or expensive stat() calls for each potential result)
   */
  assert_search ("frobni", "frobnicator.desktop\n", TRUE, FALSE, NULL, NULL);

  /* Obvious multi-word search */
  assert_search ("gno hel", "yelp.desktop\n", TRUE, TRUE, NULL, NULL);

  /* Repeated search terms should do nothing... */
  assert_search ("files file fil fi f", "nautilus.desktop\n"
                                        "gedit.desktop\n", TRUE, TRUE, NULL, NULL);

  /* "con" will match "connect" and "contacts" on name but dconf only on
   * the "config" keyword
   */
  assert_search ("con", "nautilus-connect-server.desktop gnome-contacts.desktop\n"
                        "dconf-editor.desktop\n", TRUE, TRUE, NULL, NULL);

  /* "gnome" will match "eye of gnome" from the user's directory, plus
   * matching "GNOME Clocks" X-GNOME-FullName.  It's only a comment on
   * yelp and gnome-contacts, though.
   */
  assert_search ("gnome", "eog.desktop\n"
                          "org.gnome.clocks.desktop\n"
                          "yelp.desktop gnome-contacts.desktop\n", TRUE, TRUE, NULL, NULL);

  /* eog has exec name 'false' in usr only */
  assert_search ("false", "eog.desktop\n", TRUE, FALSE, NULL, NULL);
  assert_search ("false", "", FALSE, TRUE, NULL, NULL);
  assert_search ("false", "", TRUE, TRUE, NULL, NULL);
  assert_search ("false", "", FALSE, FALSE, NULL, NULL);

  /* make sure we only search the first component */
  assert_search ("nonsearchable", "", TRUE, FALSE, NULL, NULL);

  /* "gnome con" will match only gnome contacts; via the name for
   * "contacts" and the comment for "gnome"
   */
  assert_search ("gnome con", "gnome-contacts.desktop\n", TRUE, TRUE, NULL, NULL);

  /* make sure we get the correct kde4- prefix on the application IDs
   * from subdirectories
   */
  assert_search ("konq", "kde4-konqbrowser.desktop\n", TRUE, TRUE, NULL, NULL);
  assert_search ("kate", "kde4-kate.desktop\n", TRUE, TRUE, NULL, NULL);

  /* make sure we can look up apps by name properly */
  assert_info ("kde4-kate.desktop",
               "kde4-kate.desktop\n"
               "Kate\n"
               "Kate\n"
               "nil\n", TRUE, TRUE, NULL, NULL);

  assert_info ("nautilus.desktop",
               "nautilus.desktop\n"
               "Files\n"
               "Files\n"
               "Access and organize files\n", TRUE, TRUE, NULL, NULL);

  /* make sure localised searching works properly */
  assert_search ("foliumi", "nautilus.desktop\n"
                            "kde4-konqbrowser.desktop\n"
                            "eog.desktop\n", TRUE, FALSE, "en_US.UTF-8", "eo");
  /* the user's eog.desktop has no translations... */
  assert_search ("foliumi", "nautilus.desktop\n"
                            "kde4-konqbrowser.desktop\n", TRUE, TRUE, "en_US.UTF-8", "eo");
}

static void
test_implements (void)
{
  /* Make sure we can find our search providers... */
  assert_implementations ("org.gnome.Shell.SearchProvider2",
                       "gnome-music.desktop gnome-contacts.desktop eog.desktop",
                       TRUE, FALSE);

  /* And our image acquisition possibilities... */
  assert_implementations ("org.freedesktop.ImageProvider",
                       "cheese.desktop",
                       TRUE, FALSE);

  /* Make sure the user's eog is properly masking the system one */
  assert_implementations ("org.gnome.Shell.SearchProvider2",
                       "gnome-music.desktop gnome-contacts.desktop",
                       TRUE, TRUE);

  /* Make sure we get nothing if we have nothing */
  assert_implementations ("org.gnome.Shell.SearchProvider2", "", FALSE, FALSE);
}

static void
assert_shown (const gchar *desktop_id,
              gboolean     expected,
              const gchar *xdg_current_desktop)
{
  gchar *result;

  result = run_apps ("should-show", desktop_id, TRUE, TRUE, NULL, NULL, xdg_current_desktop);
  g_assert_cmpstr (result, ==, expected ? "true\n" : "false\n");
  g_free (result);
}

static void
test_show_in (void)
{
  assert_shown ("gcr-prompter.desktop", FALSE, NULL);
  assert_shown ("gcr-prompter.desktop", FALSE, "GNOME");
  assert_shown ("gcr-prompter.desktop", FALSE, "KDE");
  assert_shown ("gcr-prompter.desktop", FALSE, "GNOME:GNOME-Classic");
  assert_shown ("gcr-prompter.desktop", TRUE, "GNOME-Classic:GNOME");
  assert_shown ("gcr-prompter.desktop", TRUE, "GNOME-Classic");
  assert_shown ("gcr-prompter.desktop", TRUE, "GNOME-Classic:KDE");
  assert_shown ("gcr-prompter.desktop", TRUE, "KDE:GNOME-Classic");
  assert_shown ("invalid-desktop.desktop", TRUE, "GNOME");
  assert_shown ("invalid-desktop.desktop", FALSE, "../invalid/desktop");
  assert_shown ("invalid-desktop.desktop", FALSE, "../invalid/desktop:../invalid/desktop");
}

static void
on_launch_started (GAppLaunchContext *context, GAppInfo *info, GVariant *platform_data, gpointer data)
{
  gboolean *invoked = data;

  g_assert_true (G_IS_APP_LAUNCH_CONTEXT (context));
  g_assert_true (G_IS_APP_INFO (info));
  /* Our default context doesn't fill in any platform data */
  g_assert_null (platform_data);

  g_assert_false (*invoked);
  *invoked = TRUE;
}

/* Test g_desktop_app_info_launch_uris_as_manager() and
 * g_desktop_app_info_launch_uris_as_manager_with_fds()
 */
static void
test_launch_as_manager (void)
{
  GDesktopAppInfo *appinfo;
  GError *error = NULL;
  gboolean retval;
  const gchar *path;
  gboolean invoked = FALSE;
  GAppLaunchContext *context;

  if (g_getenv ("DISPLAY") == NULL || g_getenv ("DISPLAY")[0] == '\0')
    {
      g_test_skip ("No DISPLAY.  Skipping test.");
      return;
    }

  path = g_test_get_filename (G_TEST_BUILT, "appinfo-test.desktop", NULL);
  appinfo = g_desktop_app_info_new_from_filename (path);

  if (appinfo == NULL)
    {
      g_test_skip ("appinfo-test binary not installed");
      return;
    }

  context = g_app_launch_context_new ();
  g_signal_connect (context, "launch-started",
                    G_CALLBACK (on_launch_started),
                    &invoked);
  retval = g_desktop_app_info_launch_uris_as_manager (appinfo, NULL, context, 0,
                                                      NULL, NULL,
                                                      NULL, NULL,
                                                      &error);
  g_assert_no_error (error);
  g_assert_true (retval);
  g_assert_true (invoked);

  invoked = FALSE;
  retval = g_desktop_app_info_launch_uris_as_manager_with_fds (appinfo,
                                                               NULL, context, 0,
                                                               NULL, NULL,
                                                               NULL, NULL,
                                                               -1, -1, -1,
                                                               &error);
  g_assert_no_error (error);
  g_assert_true (retval);
  g_assert_true (invoked);

  g_object_unref (appinfo);
  g_assert_finalize_object (context);
}

int
main (int   argc,
      char *argv[])
{
  /* While we use %G_TEST_OPTION_ISOLATE_DIRS to create temporary directories
   * for each of the tests, we want to use the system MIME registry, assuming
   * that it exists and correctly has shared-mime-info installed. */
  g_content_type_set_mime_dirs (NULL);

  g_test_init (&argc, &argv, G_TEST_OPTION_ISOLATE_DIRS, NULL);

  g_test_add_func ("/desktop-app-info/delete", test_delete);
  g_test_add_func ("/desktop-app-info/default", test_default);
  g_test_add_func ("/desktop-app-info/fallback", test_fallback);
  g_test_add_func ("/desktop-app-info/lastused", test_last_used);
  g_test_add_func ("/desktop-app-info/extra-getters", test_extra_getters);
  g_test_add_func ("/desktop-app-info/actions", test_actions);
  g_test_add_func ("/desktop-app-info/search", test_search);
  g_test_add_func ("/desktop-app-info/implements", test_implements);
  g_test_add_func ("/desktop-app-info/show-in", test_show_in);
  g_test_add_func ("/desktop-app-info/launch-as-manager", test_launch_as_manager);

  return g_test_run ();
}
