# Learning Formal Verification

Theorem proving with Lean and specifying systems with TLA+.

## Lean

### Getting Started
- [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/) - Official tutorial. The starting point.
- [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/) - David Thrane Christiansen. Lean as a programming language, not just a prover.
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/) - Jeremy Avigad et al. Formalizing math with Mathlib.
- [The Mechanics of Proof](https://hrmacbeth.github.io/math2001/) - Heather Macbeth. Intro to proof via Lean 4.
- [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4) - Learn Lean by proving properties of natural numbers. Interactive, fun.

### Intermediate
- [Metaprogramming in Lean 4](https://leanprover-community.github.io/lean4-metaprogramming-book/) - Writing tactics and automation.
- [Mathlib Documentation](https://leanprover-community.github.io/mathlib4_docs/) - The main math library for Lean 4. Enormous and growing.
- [Lean 4 Source Code](https://github.com/leanprover/lean4) - Reading the compiler and standard library.
- [Hitchhiker's Guide to Logical Verification](https://browncs1951x.github.io/static/lectures/hitchhikersguide.pdf) - Baanen, Bentkamp, Blanchette et al. Lean 4 edition.

### Advanced
- [Certified Programming with Dependent Types](http://adam.chlipala.net/cpdt/) - Adam Chlipala. Written for Coq but concepts transfer directly to Lean.
- [The Lean 4 Type System](https://arxiv.org/abs/2407.00983) - Ullrich & de Moura. Lean 4's type theory explained.
- [Lean Together Workshops](https://leanprover-community.github.io/events.html) - Recordings and materials from community events.

### Lean for Verified Software
- [Verified Functional Programming in Agda](https://www.amazon.com/Verified-Functional-Programming-Agda-Books/dp/1970001240) - Stump. Concepts applicable to Lean.
- [Lean for Hackers](https://lean-lang.org/lean4/doc/) - Official reference manual.
- [LeanSAT](https://github.com/leanprover/leansat) - SAT solving in Lean.
- [SciLean](https://github.com/lecopivo/SciLean) - Scientific computing in Lean.

### Papers on Lean
- [The Lean 4 Theorem Prover and Programming Language](https://leanprover.github.io/lean4/doc/lean4.pdf) - de Moura & Ullrich. System description.
- [Tactic Metaprogramming in Lean 4](https://arxiv.org/abs/2410.17113) - Extending Lean's tactic framework.
- [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](https://arxiv.org/abs/2306.15626) - Yang et al. (2023). AI-assisted proving in Lean.
- [A Promising Path Towards Autoformalization and General Artificial Intelligence](https://arxiv.org/abs/2305.10366) - Yuhuai Wu et al. LLMs + Lean.

### Lean Community
- [Lean Zulip Chat](https://leanprover.zulipchat.com/) - The main community hub. Very active and welcoming.
- [Mathlib Contributions Guide](https://leanprover-community.github.io/contribute/) - How to contribute to Mathlib.
- [Lean 4 Examples](https://github.com/leanprover/lean4-samples) - Official sample projects.

## TLA+

### Getting Started
- [Specifying Systems](https://lamport.azurewebsites.net/tla/book.html) - Leslie Lamport. Free online. The definitive reference.
- [Learn TLA+](https://learntla.com/) - Hillel Wayne. Practical, example-driven introduction.
- [TLA+ Video Course](http://lamport.azurewebsites.net/video/videos.html) - Lamport's own video lectures.
- [PlusCal Manual](https://lamport.azurewebsites.net/tla/p-manual.pdf) - Lamport. PlusCal is an algorithm language that compiles to TLA+.

### Intermediate
- [Practical TLA+](https://www.amazon.com/Practical-TLA-Planning-Driven-Development/dp/1484238281) - Hillel Wayne. Book with hands-on examples.
- [TLA+ Examples](https://github.com/tlaplus/Examples) - Official repository of TLA+ specifications.
- [Dr. TLA+ Series](https://github.com/tlaplus/DrTLAPlus) - Lectures on distributed algorithms specified in TLA+.

### Papers
- [The Temporal Logic of Actions](https://lamport.azurewebsites.net/pubs/lamport-actions.pdf) - Lamport (1994). The original TLA paper.
- [Who Builds a House without Drawing Blueprints?](https://cacm.acm.org/magazines/2015/4/184705-who-builds-a-house-without-drawing-blueprints/fulltext) - Lamport (2015). Why formal specification matters.
- [Use of Formal Methods at Amazon Web Services](https://lamport.azurewebsites.net/tla/formal-methods-amazon.pdf) - Newcombe et al. (2015). TLA+ in production at AWS.
- [How Amazon Web Services Uses Formal Methods](https://cacm.acm.org/magazines/2015/4/184701-how-amazon-web-services-uses-formal-methods/fulltext) - Newcombe et al. CACM version.

### TLA+ for Distributed Systems
- [Paxos Made Simple](https://lamport.azurewebsites.net/pubs/paxos-simple.pdf) - Lamport. The classic, with TLA+ spec available.
- [Raft TLA+ Specification](https://github.com/ongardie/raft.tla) - Formal specification of the Raft consensus protocol.
- [CockroachDB's Use of TLA+](https://www.cockroachlabs.com/blog/parallel-commits/) - How CockroachDB uses TLA+ for correctness.
- [Elasticsearch Formal Models](https://github.com/elastic/elasticsearch-formal-models) - TLA+ specs for Elasticsearch protocols.

## Verified Distributed Systems (Papers)

- [IronFleet: Proving Practical Distributed Systems Correct](https://www.andrew.cmu.edu/user/bparno/papers/ironfleet.pdf) - Hawblitzel et al. (2015). End-to-end verified distributed system.
- [Verdi: A Framework for Implementing and Formally Verifying Distributed Systems](https://homes.cs.washington.edu/~ztatlock/pubs/verdi-wilcox-pldi15.pdf) - Wilcox et al. (2015).
- [Chapar: Certified Causally Consistent Distributed Key-Value Stores](https://www.cs.purdue.edu/homes/bendy/Chapar/) - Lesani et al. (2016).

## Tools

- [TLA+ Toolbox](https://github.com/tlaplus/tlaplus) - IDE for TLA+ with TLC model checker.
- [Lean 4](https://github.com/leanprover/lean4) - The Lean 4 theorem prover.
- [Mathlib4](https://github.com/leanprover-community/mathlib4) - The main math library for Lean 4.
- [TLAPS](https://tla.msr-inria.inria.fr/tlaps/content/Home.html) - TLA+ Proof System for machine-checked proofs.
