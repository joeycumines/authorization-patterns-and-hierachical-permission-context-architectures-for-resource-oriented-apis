# General Authorization Implementation Patterns & Hierarchical Permission-Context Architectures for Resource-Oriented APIs

Specification: https://joeycumines.github.io/authorization-patterns-and-hierachical-permission-context-architectures-for-resource-oriented-apis/

tl;dr: Innovative application of two complementary insights:

1. What business need of "roles" frequently map well to declarative, pure-function definitions of permission scopes, e.g. these (oversimplified) hypotheticals:
    1. "team member of team A" able to create, update, and execute, but not delete or administrate resources, within team A
    2. "company admin of company C" able to administrate a company C but not company B or any other company

2. Advisory client-side checks with zero (amortised) cost may be achieved by leveraging low per-Actor permission scope cardinality as the scope for permission context resolution

In most cases all you need to do is attach access classes to methods, then you're done. Now your services authorize declaratively and frontends can trivially check what is available to call.

## Background

"Uncook authorization, or at least make it not completely terrible and / or broken" - sound familiar?
That, in the context of B2B SaaS, was the first problem I encountered (as a professional) which I was unable to readily - with moderate time and substantial effort - produce a solution that left me confident it was *at least* sound and defensible.

It irked me, to be honest. *Why* does authz in particular always seem to devolve into poorly-maintained, seemingly ill-conceived series of switching cases, at best distributed across both the frontend *and* backend surfaces? *Why* is it so "obvious" that we'd likely only need company and team level permission scopes?
Surely not, I thought, and after no one was able to help me understand their (to me) nonsensical position, this, too, irked me.
Forced to conclude I was missing something, I settled on mapping the common (B2B) concepts of "company" and "team" to a simple, downwards-propagating, hierarchical permission model.
With my wealth of "wisdom and experience" I'm - now - confident this model is both sound and defensible, and, in many cases, optimal - with the right approach. The right approach is what this project aims to provide.

The primary contents of this repository - [index.html](index.html) - provide a deliberately narrow implementation pattern tailored for my preferred way to implement APIs - building resource-oriented APIs as per Google's [AIPs](https://google.aip.dev/general).
I conceptualized and refined this approach *multiple times* over the course of my career, yet never had sufficient cause to take it beyond my personal notes.
This has led to *many* "relearning" moments, hence, I figured it was time to formalize the approach. Seriously, I've reached the same conclusion from first principles multiple times.

## Disclaimer

With today's AI models, I've found reliable success in turning my intuition re: problems I previously struggled to solve without an extended period of, well, fixation, into solutions I feel comfortable with and have confidence in even without repeated iterations and trials in real production contexts.
Nevertheless, I caution any reader to heed the following: The AI went ham, above and beyond the core patterns, ideas, and understanding, which I personally provided, and your milage may vary. If this approach kicks your dog, breaks your favorite mug, or otherwise causes you harm, please seek help from an... appropriately-qualified professional.
