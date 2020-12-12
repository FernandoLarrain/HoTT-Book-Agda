# Pending

* Results about binary functions, including
  * Simultaneous action on paths
  * Iterated function extensionality
  * Transport along function extensionality

* Direct map from quasi-inverses to equivalences

* Add right-unit law for paths in the other direction

* Use modules (open using / hiding / renaming) and equational reasoning to increase readability of proofs.

* Clean Ch2.Exercise.

* Implement equivalence relations (including equational reasoning) as a type class.

* Systematize description of path-spaces of type constructors (intro, elim, beta and eta rules). Similarly for univalence, function extensionality, propositional truncations, etc. Perhaps use records. Describe how action on paths and transport work on the equivalent descriptions.

* Systematize HITs, perhaps using records. See Generic1HIT in HoTT std. lib.

* Study std. lib. in detail to import other ideas.

* Prove groupoid laws for homotopies (using equality or homotopy?) and equivalence relations.

* Whiskering should bind more loosely than concatenation

* Remove named implicit arguments

* Modules with equivalence: .equiv

* Finish / fix 2.14 (maybe change to magmas; the full associativity proof is in M. Escardo's notes.

* Define equivalence with old 1-type definition

* Use PROP and SET?

* Improve readability of univalence and funext modules

* Change where-lemmas to sublemmas

* Generalize constructions that restrict to a single universe when possible. Restrict theorem hypotheses, not definitions (unless multiverse definitions don't make sense). E.g. N-Algebras in Ch5.

* Results about the relation between path spaces in fibers and ap in Ch4.2 and "propositional maps" in Ch4.6 should be postponed until Ch7.

* Develop groupoid structure and whiskering operations for homotopies.

* Redefine retraction and section to be just witnesses of invertibility. Retract suffice for naming the triple.

* Derive equivalences from quasi-inverse results to avoid repeated construction of equivalences.

* Homotopy preserves isequiv.

* inv preserves isequiv.

* Homotopy and inv commute.

* Section and retraction commutative triangles.

* Functorial action of products, coproducts and universe lifting.

* Spans, cones, cocones, functorial action of pullbacks and pushouts.

* Constant function

* Singleton induction

* Unwhiskering operations and whiskering operations for homotopies

* Rename \Sigma-over-Contr and \Sigma-of-Contr as left and right unit laws

* Define maps over / total over (at least for thesis)

* Fix Ch4.1. Does opening PropTrunc publicly help?

* Prove 2-groupoid laws for whiskering and horizontal composition operations

* Use rewrite only when necessary. Propositional computation rules suffice for UMPs.

* Simplify lifting arguments using universe polymorphism (see, e.g., UMP of products in Ch2.15).

* Universe polymorphism is used explicitly in some proofs about inductive principles / universal mapping properties. To get actual equivalences (rather than mere logical equivalences) it is best to avoid it and use lifting or multiple hypotheses.

* Fix performance issues with funext and univ: passing universe explicitly seems to help a lot (see 5.8-Id-types-and-id-systems).