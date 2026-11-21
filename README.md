# General Authorization Implementation Patterns & Hierarchical Permission-Context Architectures for Resource-Oriented APIs

Specification: https://joeycumines.github.io/authorization-patterns-and-hierachical-permission-context-architectures-for-resource-oriented-apis/

tl;dr: Putting two complementary insights together, with AIP/protobuf descriptors as the single source of truth:

1. What businesses actually need from "roles" frequently maps well to scoped grants selecting resource types and access classes, evaluated (and projected) as pure functions over declared API methods - e.g. these (oversimplified) hypotheticals:
    1. "team member of team A" able to read, create, update, and execute, but not delete or administrate resources, within team A
    2. "company admin of company C" able to administrate company C, but not company B or any other company

2. Advisory client-side checks with near-zero amortised network cost (zero RTTs on cache hit) may be achieved when policy is mostly uniform within coarse scopes, by resolving permission contexts at those low-cardinality per-Actor scopes rather than per leaf resource

Once the runtime and client logic are in place, in most cases all you need to do is mark standard AIP methods as `standard` (or declare an access class and operation for custom methods), and you're done. Your services authorize the declarative bits automatically, handlers keep the state-dependent checks, and frontends can cheaply check what's available to call.

## Background

"Uncook authorization, or at least make it not completely terrible and / or broken" - sound familiar?
That, in the context of B2B SaaS, was the first problem I encountered (as a professional) which I was unable to readily - with moderate time and substantial effort - produce a solution that left me confident it was *at least* sound and defensible.

It irked me, to be honest. *Why* does authz in particular always seem to devolve into poorly-maintained, seemingly ill-conceived series of switching cases, at best distributed across both the frontend *and* backend surfaces? *Why* is it so "obvious" that we'd likely only need company and team level permission scopes?
Surely not, I thought, and after no one was able to help me understand their (to me) nonsensical position, this, too, irked me.
Forced to conclude I was missing something, I settled on mapping B2B concepts like "company" and "team" to a hierarchical, downwards-propagating permission model over the resource tree - arbitrary depth when you actually need it, but coarse scopes doing the heavy lifting so grants stay uniform enough to project and cache cheaply (at least until you get into ad-hoc per-item sharing or heavy row-level ABAC, where you want something else).
With my wealth of "wisdom and experience" I'm - now - confident this model is both sound and defensible, and, for hierarchical B2B SaaS workloads, often optimal - provided you handle the nasty bits (forbids, conditions, private rules, cache freshness) properly. That's what this project aims to provide.

The primary contents of this repository - [index.html](index.html) - pair a brief taxonomy of general authorization patterns with a deliberately narrow implementation spec (complete with protobuf contracts, a live simulator, and executable regression checks) tailored for my preferred way to implement APIs - building resource-oriented APIs as per Google's [AIPs](https://google.aip.dev/general).
I conceptualized and refined this approach *multiple times* over the course of my career, yet never had sufficient cause to take it beyond my personal notes.
This has led to *many* "relearning" moments, hence, I figured it was time to formalize the approach. Seriously, I've reached the same conclusion from first principles multiple times.

## Disclaimer

With today's AI models, I've found reliable success in turning my intuition re: problems I previously struggled to solve without an extended period of, well, fixation, into solutions I feel comfortable with and have confidence in even without repeated iterations and trials in real production contexts. In this case, even without having actually rolled it out, yet.

Nevertheless, I caution any reader to heed the following: The AI went ham, above and beyond the core patterns, ideas, and understanding, which I personally provided, and your milage may vary. If this approach kicks your dog, breaks your favorite mug, or otherwise causes you harm, please seek help from an... appropriately-qualified professional.
