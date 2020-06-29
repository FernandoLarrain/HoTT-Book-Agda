# HoTT-Book-Agda

## The Library

The structure of the library follows closely that of the book. The only nonlinearities are the dependency of `Ch1.2` on `Ch1.3` (Universes form the basis of everything else) and `Ch1.6` on `Ch1.5` (binary products are defined as a particular case of dependent-pair types). The following files are ordered lexicographically, first, by dependence, and second, by numbering.

#### Chapter 1 (src\Ch1)

1. `Ch1.3-Universes-and-families`
2. `Ch1.2-Function-types`
3. `Ch1.4-Dependent-function-types`
4. `Ch1.6-Dependent-pair-types`
5. `Ch1.5-Product-types`
6. `Ch1.7-Coproduct-types`
7. `Ch1.8-The-type-of-booleans`
8. `Ch1.9-The-natural-numbers`
9. `Ch1.11-Propositions-as-types`
10. `Ch1.12-Identity-types`

#### Chapter 2 (src\Ch2)

1. `Ch2.1-Types-are-higher-groupoids`
2. `Ch2.2-Functions-are-functors`
3. `Ch2.3-Type-families-are-fibrations`
4. `Ch2.4-Homotopies-and-equivalences`
5. `Ch2.6-Cartesian-product-types`
6. `Ch2.7-Σ-types`
7. `Ch2.8-The-unit-type`
8. `Ch2.9-Π-types-and-funext`
9. `Ch2.10-Universes-and-univalence`
10. `Ch2.11-Identity-type`
11. `Ch2.12-Coproducts`
12. `Ch2.13-Natural-numbers`
13. `Ch2.15-Universal-properties`
14. `Ch2.Exercises`

#### Chapter 3 (src\Ch3)

1. `Ch3.1-Sets-and-n-types`
2. `Ch3.2-Propositions-as-types`
3. `Ch3.3-Mere-propositions`
4. `Ch3.4-Classical-vs-intuitionistic-logic`
5. `Ch3.5-Subsets-and-prop-resizing`
6. `Ch3.6-The-logic-of-mere-props`
7. `Ch3.7-Propositional-truncation`
8. `Ch3.9-The-pple-of-unique-choice`
9. `Ch3.11-Contractibility`

#### Chapter 4 (src\Ch4)

1. `Ch4.1-Quasi-inverses`
2. `Ch4.2-Half-adjoint-equivalences`
3. `Ch4.3-Bi-invertible-maps`
4. `Ch4.4-Contractible-fibers`
5. `Ch4.6-Surjections-and-embeddings`

#### Chapter 6 (src\Ch6)

1. `Ch6.2-Induction-pples-and-dependent-paths`

#### Chapter 7 (src\Ch7)

1. `Ch7.1-Definition-of-n-types`


## Potential inconsistencies

Agda has some features that are inconsitent with HoTT. To avoid them, 

1. the absurd pattern should be used only intially for the definition of the recursion and induction principles of the empty type, and

2. every file should begin with `{-# OPTIONS --without-K #-}`

3. The following files use the `rewrite` construct: `Ch2.4`, `Ch4.2` and `Ch7.1`.

4. The `--safe` option was used until the first postulates were made (around the end of `Ch2`).


## The Axioms

1. `Ch2.9` postulates function extensionality, which is later proved from univalence in `Ch4.9` and using the interval in `Ch6.3`.

2. `Ch2.10` postulates univalence.

3. `Ch6` postulates several higher inductive types.

4. Propositional truncation is assumed via modules in `Ch3.7` (`basic-truncation-development`), `Ch3.9` (`unique-choice`) and `Ch4.6` (`surjections`, `isequiv-\simeq-is-surjective-embedding`).


## The notion of equivalence

The book uses bi-invertible maps up to `Ch4.5` and half-adjoint equivalences from then on. Accordingly, up to that point, the code works with both definitions, and from then on, only with the second.
