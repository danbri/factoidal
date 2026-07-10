// docs/web/hub-live.11ty.js — task #105's "live mode" hub twin.
//
// Auto-generates one page per numbered hub post (docs/.eleventy.js's
// `hubPosts` collection) at /web/hub-live/<slug>/, reusing that post's
// *already-rendered* `templateContent` verbatim (same markdown, same
// ```observable-js cells — "same notebook source, different
// capability" per the task) rather than duplicating or re-authoring
// any post. This is the "eleventy pagination... alias" mechanism the
// task asked for: least duplication eleventy supports for an N-page
// twin of an existing collection, one class, no copy of any post's
// prose.
//
// The ONLY behavioural difference between a post and its twin is the
// `hubMode: "live"` data value threaded through to docs/_includes/
// hub.njk (both pages share that one layout) — see hub.njk's CSP meta
// tag, live-mode banner, <base href>, and `data-hub-mode` body
// attribute, all conditioned on `hubMode`. Post 21's map cell reads
// that same `data-hub-mode` attribute at runtime to decide whether to
// add an OSM raster tile layer on top of the vendored vector basemap
// (strict mode never does — see
// docs/web/hub/21-geosparql-geometry-and-topology.md).
module.exports = class {
  data() {
    return {
      pagination: {
        data: "collections.hubPosts",
        size: 1,
        alias: "post",
      },
      layout: "hub.njk",
      hubMode: "live",
      // Live twins are a *view* of an existing post, not a new post in
      // their own right — keep them out of collections.all/hubPosts so
      // nothing (a future "list every hub post" page, an RSS feed,
      // hub_browser_all.sh's directory-listing enumeration under
      // web/hub/) ever picks them up as if they were independent
      // content. hub_browser_all.sh already only walks web/hub/ (not
      // web/hub-live/) so this is belt-and-suspenders, not load-bearing
      // for that harness specifically.
      eleventyExcludeFromCollections: true,
      eleventyComputed: {
        permalink: (data) => `web/hub-live/${data.post.fileSlug}/index.html`,
        title: (data) => data.post.data.title,
        description: (data) => data.post.data.description,
        series: (data) => data.post.data.series,
        series_order: (data) => data.post.data.series_order,
        vocab: (data) => data.post.data.vocab,
        // hub.njk's live banner + <base href> point back at the strict
        // original via `livePostSlug` — the ONE piece of per-post
        // state the layout needs that isn't already on `post`/`page`
        // in strict mode (there, `page.fileSlug` IS the post's own
        // slug; here, `page.fileSlug` would be this pagination page's
        // own file, "hub-live", so the layout can't reuse it).
        livePostSlug: (data) => data.post.fileSlug,
      },
    };
  }

  render(data) {
    return data.post.templateContent;
  }
};
