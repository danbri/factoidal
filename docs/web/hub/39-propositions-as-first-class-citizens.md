---
title: "Propositions as first-class citizens"
description: "Withdrawn pending a reversibility theorem for the IKL-to-RDF projection this post demonstrated."
layout: hub.njk
series: docs-hub
series_order: 39
vocab: none
status: withdrawn
---

## This post is withdrawn

This post demonstrated Factoidal's projection of IKL propositions into
RDF named graphs — the `urn:cl:that:sha256:` content-addressed
proposition naming, and the `urn:cl:def:asserts` / `urn:cl:def:rdfProjection`
/ `urn:cl:def:sentence` vocabulary the projection used to decorate
those graphs. Those naming and decoration conventions are not yet
justified: there is no proof that projecting RDF into IKL and back
recovers the original data (a `rdf → ikl → rdf` reversibility
theorem), so the post was presenting unsettled conventions as if they
were a finished feature.

Tracking issue: [danbri/factoidal#620](https://github.com/danbri/factoidal/issues/620).

The post will be restored, rewritten around the reversibility
theorem's own demo, once that theorem lands. Until then, see [post
41](../41-a-walkthrough-of-the-ikl-guide/) for what the CLIF reader
does today: it parses Common Logic and IKL sentences — including
`(that S)` proposition terms — and reports their structure. It does
not project them into RDF on this site anymore.
