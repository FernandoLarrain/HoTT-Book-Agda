# HoTT-Book-Agda

## Authorship

Most of the formalizations in this library are original. However, while learning Agda and setting up the library, I imported code and ideas from other sources (in addition to, of course, the [HoTT Book](https://homotopytypetheory.org/book/)). It is, at this point, impossible for me to demarcate them precisely, because they have been modified and reorganized multiple times. However, I can provide a rough guide to where they played an essential role:

1. [Martín Escardó's Lecture Notes](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/index.html): fundamental notions, axioms and notation.
2. [The HoTT-Agda Library](https://github.com/HoTT/HoTT-Agda): basics of rewriting and Higher Inductive Types.
3. [Egbert Rijke's HoTT-Intro](https://github.com/EgbertRijke/HoTT-Intro): ideas about Singleton Induction and the Fundamental Theorem of Identity Types.

## The library

The structure of the library follows closely that of the HoTT Book. The only nonlinearities are the dependency of `Ch1.2` on `Ch1.3` (universes form the basis of everything else), `Ch1.6` on `Ch1.5` (binary products are defined as a particular case of dependent-pair types), `Ch4.1` on `Ch4` and `Ch6.8` on `Ch6.9`. The following files are ordered lexicographically, first, by dependence, and second, by numbering.

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
6. `7-Î£-types`
7. `8-The-unit-type`
8. `9-Î -types-and-funext`
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

1. `2-Half-adjoint-equivalences`
2. `3-Bi-invertible-maps`
3. `4-Contractible-fibers`
4. `6-Surjections-and-embeddings`
5. `7-Closure-properties-of-equivalences`
6. `8-The-object-classifier`
7. `9-Univalence-implies-funext`
6. `Exercises`
7. `1-Quasi-inverses`

The file `Equivalences` imports `Ch4` (except `1-Quasi-inverses`).

### Chapter 5 (src\Ch5)

1. `1-Introduction-to-inductive-types`
2. `3-W-types`
3. `4-Inductive-types-are-initial-algebras`
4. `8-Id-types-and-id-systems`
5. `Exercises`

The file `Induction` imports `Ch4`. 

#### Chapter 6 (src\Ch6)

1. `2-Induction-pples-and-dependent-paths`
2. `3-The-interval`
3. `4-Circles-and-spheres-safe`
4. `4-Circles-and-spheres`
5. `5-Suspensions-safe`
6. `5-Suspensions`
7. `9-Truncations`
8. `8-Pushouts`
9. `10-Quotients`
10. `11-Algebra`
11. `Exercises`

#### Chapter 7 (src\Ch7)

1. `1-Definition-of-n-types`
2. `2-UIP-and-Herberg's-theorem-safe`
3. `2-UIP-and-Hedberg's-theorem`
4. `3-Truncations-safe`
5. `3-Truncations`
6. `5-Connectedness`
7. `6-Orthogonal-factorization`


## Potential inconsistencies

Agda has some features that are inconsitent with HoTT. To avoid them, 

1. the absurd pattern should be used only intially for the definition of the recursion and induction principles of the empty type, and

2. every file should begin with `{-# OPTIONS --without-K #-}`.

## The axioms

1. Function Extensionality is assumed via instance arguments until it is derived from Univalence in Ch4.9. Instance arguments generate some performance issues. 

2. Univalence is postulated in Ch2.

3. Propositional and set truncations are assumptions until they are derived from Higher Inductive Types in Ch7.

4. Higher Inductive Types with definitional equality for point constructors have to be postulated together with a rewrite relation which is defined in the file `Rewrite`.

## The notion of equivalence

The book uses bi-invertible maps up to `Ch4.5` and half-adjoint equivalences from then on. Accordingly, up to that point, the code works with both definitions, and from then on, only with the second. The default is the new definition. To use the old one, change `open new-equiv public` to `open old-equiv public` in `Ch2.4`.