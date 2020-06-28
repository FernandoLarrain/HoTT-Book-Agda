hott-book library

1. The Library
==============

The structure of the library follows closely that of the book. The only nonlinearities are the dependency of Ch1.2 on Ch1.3 (Universes form the basis of everything else) and Ch1.6 on Ch1.5 (binary products are defined as a particular case of dependent-pair types). The following files are ordered lexicographically, first, by dependence, and second, by numbering.

Chapter 1 (src\Ch1)

Ch1.3-Universes-and-families
Ch1.2-Function-types
Ch1.4-Dependent-function-types
Ch1.6-Dependent-pair-types
Ch1.5-Product-types
Ch1.7-Coproduct-types
Ch1.8-The-type-of-booleans
Ch1.9-The-natural-numbers
Ch1.11-Propositions-as-types
Ch1.12-Identity-types

Chapter 2 (src\Ch2)

Ch2.1-Types-are-higher-groupoids
Ch2.2-Functions-are-functors
Ch2.3-Type-families-are-fibrations
Ch2.4-Homotopies-and-equivalences
Ch2.6-Cartesian-product-types
Ch2.7-Σ-types
Ch2.8-The-unit-type
Ch2.9-Π-types-and-funext
Ch2.10-Universes-and-univalence
Ch2.11-Identity-type
Ch2.12-Coproducts
Ch2.13-Natural-numbers
Ch2.15-Universal-properties
Ch2.Exercises

Chapter 3 (src\Ch3)

Ch3.1-Sets-and-n-types
Ch3.2-Propositions-as-types
Ch3.3-Mere-propositions
Ch3.4-Classical-vs-intuitionistic-logic
Ch3.5-Subsets-and-prop-resizing
Ch3.6-The-logic-of-mere-props
Ch3.7-Propositional-truncation
Ch3.9-The-pple-of-unique-choice
Ch3.11-Contractibility

Chapter 4 (src\Ch4)

Ch4.1-Quasi-inverses
Ch4.2-Half-adjoint-equivalences
Ch4.3-Bi-invertible-maps
Ch4.4-Contractible-fibers
Ch4.6-Surjections-and-embeddings

Chapter 6 (src\Ch6)

Ch6.2-Induction-pples-and-dependent-paths

Chapter 7 (src\Ch7)

Ch7.1-Definition-of-n-types


2. Potential inconsistencies
============================

Agda has some features that are inconsitent with HoTT. To avoid them, 

i) the absurd pattern should be used only intially for the definition of the recursion and induction principles of the empty type, and

ii) every file should begin with {-# OPTIONS --without-K #-}

iii) The following files use the rewrite construct: Ch2.4, Ch4.2 and Ch7.1.

iv) The --safe option was used until the first postulates were made (around the end of Ch2).


3. The Axioms
=============

i) Ch2.9 postulates function extensionality, which is later proved from univalence in Ch4.9 and using the interval in Ch6.3.

ii) Ch2.10 postulates univalence.

iii) Ch6 postulates several higher inductive types.

iv) Propositional truncation is assumed via modules in Ch3.7 (basic-truncation-development), Ch3.9 (unique-choice) and Ch4.6 (surjections, isequiv-\simeq-is-surjective-embedding).


4. The notion of equivalence
============================

The book uses bi-invertible maps up to Ch4.5 and half-adjoint equivalences from then on. Accordingly, up to that point, the code works with both definitions, and from then on, only with the second.