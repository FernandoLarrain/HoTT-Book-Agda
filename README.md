# HoTT-Book-Agda

## The Library

The structure of the library follows closely that of the book. The only nonlinearities are the dependency of `Ch1.2` on `Ch1.3` (universes form the basis of everything else) and `Ch1.6` on `Ch1.5` (binary products are defined as a particular case of dependent-pair types). The following files are ordered lexicographically, first, by dependence, and second, by numbering.

#### Chapter 1 (src\Ch1)

1. `3-Universes-and-families`
2. `2-Function-types`
3. `4-Dependent-function-types`
4. `6-Dependent-pair-types`
5. `5-Product-types`
6. `7-Coproduct-types`
7. `8-The-type-of-booleans`
8. `9-The-natural-numbers`
9. `11-Propositions-as-types`
10. `12-Identity-types`

The file `Type-theory` imports `Ch1`.

#### Chapter 2 (src\Ch2)

1. `1-Types-are-higher-groupoids`
2. `2-Functions-are-functors`
3. `3-Type-families-are-fibrations`
4. `4-Homotopies-and-equivalences`
5. `6-Cartesian-product-types`
6. `7-Σ-types`
7. `8-The-unit-type`
8. `9-Π-types-and-funext`
9. `10-Universes-and-univalence`
10. `11-Identity-type`
11. `12-Coproducts`
12. `13-Natural-numbers`
13. `14-Equality-of-structures`
13. `15-Universal-properties`
14. `Exercises`

The file `Homotopy-type-theory` imports `Ch2`.

#### Chapter 3 (src\Ch3)

1. `1-Sets-and-n-types`
2. `2-Propositions-as-types`
3. `3-Mere-propositions`
4. `4-Classical-vs-intuitionistic-logic`
5. `5-Subsets-and-prop-resizing`
6. `6-The-logic-of-mere-props`
7. `7-Propositional-truncation`
8. `9-The-pple-of-unique-choice`
9. `11-Contractibility`
10. `Exercises`

The file `Sets-and-logic` imports `Ch3`.

#### Chapter 4 (src\Ch4)

1. `1-Quasi-inverses`
2. `2-Half-adjoint-equivalences`
3. `3-Bi-invertible-maps`
4. `4-Contractible-fibers`
5. `6-Surjections-and-embeddings`
6. `7-Closure-properties-of-equivalences`

### Chapter 5 (src\Ch5)

1. `1-Introduction-to-inductive-types`
2. `3-W-types`
3. `4-Inductive-types-are-initial-algebras`

#### Chapter 6 (src\Ch6)

1. `2-Induction-pples-and-dependent-paths`
2. `3-The-interval`
3. `4-Circles-and-spheres`

#### Chapter 7 (src\Ch7)

1. `Ch7.1-Definition-of-n-types`
2. `UIP-and-Hedberg's-theorem`


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

The book uses bi-invertible maps up to `Ch4.5` and half-adjoint equivalences from then on. Accordingly, up to that point, the code works with both definitions, and from then on, only with the second. The default is the new definition. To use the old one, change `open new-equiv public` to `open old-equiv public` in `Ch2.4`.
