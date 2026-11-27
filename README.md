# Lean formalization of the strict path model

This project formalizes the strict path algebra underlying Sections 2--4 of
`general_sphere_T_syzygy_zh.tex`.  The concrete Section 2 comparison and the
complete cone-vanishing argument of Section 3 are now mechanically checked.
The development uses the literal quotient by zero increments;
in particular, it never imposes additivity in an increment label.

## Mechanically checked so far

- `PathAlgebra`: free integral distributions, the quotient relation
  `[0; x] = 0`, descended boundary, and the normalized three-term formula.
- `Functoriality`, `Normalization`, and `ReducedBoundary`: pushforward,
  augmentation-zero targets, base normalization, and the fully typed identity
  `d_* ∂ = ∂ d_*` from (2.9).
- `Subdivision` and `SubdivisionNaturality`: ordered coordinate subdivision,
  both primitive and physical boundary identities in (2.14), the `d_*`
  naturality square, the canonical path `p_*`, and `∂ p_* = 1` from (2.16).
- `CoordinateRestriction`: restriction literally deletes coordinates and
  inherits their ambient order; ordered paths, subdivision, and `p_*` commute
  strictly with this operation, and `p_*` preserves coordinate-local vanishing.
- `ElementaryPaths` and `ElementaryNaturality`: the exact subgroup generated
  by nonzero one-coordinate hoppings; subdivision and `p_*` are corestricted to
  this subgroup, and all three identities in (2.14) retain their sharpened
  codomains.
- `Cells` and `SquareStrip`: base translation, squares and triangles, their
  zero boundaries, (2.32), and the arbitrary-finite-word form of the
  square-strip identity (3.16).
- `CubeBasis`, `CubeReduced`, `CubeRestriction`, and `CubeKernel`: the explicit
  cubes `Q(c)`, Boolean expansion and Möbius inversion, integral bases of both
  the free and augmentation-zero distribution groups, the two possible
  restriction behaviors, and the full common-kernel decomposition (2.20).
  Together these give the tensor-free proof of (2.19)--(2.21).
- `PrimitiveQuotient`: facet restriction data, locally-zero subgroups as
  intersections of kernels, the literal groups `Rprim`, `Zprim`, and `Bprim`,
  the inclusion `Bprim ≤ Zprim`, and the quotient `TPrime = Zprim / Bprim`
  from (2.10)--(2.12).
- `LocalIdentity`, `PhysicalQuotientCore`, and `IteratedLocality`: the
  no-common-facet predicate, arbitrary iterated base differences, the exact
  physical numerator and full basic-locality denominator, and the typed
  quotient `T = E_inv / E_id` (including every `k >= 0`).
- `DistributionDifferences`, `ReducedLocalKernel`, and `ZeroIdentityImage`:
  raw finite differences on arbitrary free distributions, the exact reduced
  common-restriction kernel, and the complete image equality (2.25)
  `d_* Dbar_inv = D_id` for a surjective coboundary map.
- `TauQuotient`: the physical locally-zero reduced-distribution numerator
  `D_inv`, the direct inclusion `D_id <= D_inv`, and the typed quotient
  `Tau = D_inv / D_id`.
- `PrimitiveIdentityLift`: the full easy inclusion in (2.26): every iterated
  physical locality identity has an elementary, closed, locally-zero
  primitive lift.
- `SameCoordinateIdentity` and `CoordinateLocalityBridge`: the literal
  three-square formula (2.32), all zero-label degeneracies, stability under
  the remaining finite differences, and the derivation of all three abstract
  locality hypotheses from the paper's single coordinate-support condition.
- `OrderedFilling` and `OrderedFillingNaturality`: the finite-coordinate
  induction behind (2.28): adjoining one elementary edge to the canonical
  ordered path differs from the new canonical path by an integral span of
  transverse squares and same-coordinate triangles; the span is closed and
  stable under coordinate restriction, while the final loop obeys the strict
  restriction formula from (2.30).
- `OperatorCoefficients` and `CoefficientLocalZero`: a genuine quotient-level
  coefficient extractor for each nonzero oriented elementary label, its
  translation/difference/cell formulas, the correct singleton-fiber
  restriction theorem, and the deduction that every visible-label coefficient
  distribution of a locally-zero elementary path vanishes on all visible
  facets.
- `PrimitiveCellChains`, `ExplicitOrderedCellFilling`, and
  `ExplicitFillingNaturality`: a free integral module on the complete
  transverse-square and same-coordinate-triangle types, its degree-two
  boundary and type coefficient distributions, an explicit positive-sign
  two-chain filling each ordered elementary-edge loop, and strict naturality
  of that selected chain under coordinate restriction.
- `ElementaryCellChainFilling` and `CellTypeLocalZero`: honest two-chain
  existence for every elementary path with boundary
  `p - p_*(∂p)`, together with the exact statement that every complete cell
  type of a facetwise-zero two-chain has a base distribution in the common
  visible-facet restriction kernel.
- `ExplicitFillingMap`: a choice-free linear version of the ordered filling
  `H`, with its boundary formula and strict coordinate-restriction
  naturality on the elementary subgroup.
- `CellTypeBoundaryDecomposition`, `TransverseCellImage`,
  `TriangleCellImage`, `ClosedPrimitiveImage`, and
  `ClosedPrimitiveIdentityImage`: finite complete-type decomposition of the
  filling boundary, the transverse-square and same-coordinate-triangle
  locality calculations, the hard inclusion, and the full equality (2.26).
- `CoordinatePathLocality` and `PrimitiveToPhysicalQuotient`: locality of
  canonical paths and subdivision, followed by the fully descended forward
  comparison map (2.35), including its representative formula.
- `PhysicalToPrimitiveQuotient`: an exact interface for the remaining
  relative primitive lift, the reverse quotient map (2.34), both inverse
  identities, the linear equivalence `T ≃ TPrime`, and proof that both its
  reverse map and the resulting equivalence are independent of the chosen
  admissible lift.
- `RelativePrimitiveSection`: the actual algebraic bridge from the
  set-theoretic primitive sections produced by (2.22)--(2.24) to the required
  linear path lift.  It works directly on elementary edge generators, so no
  additive section or separate coefficient-reassembly hypothesis is needed.
- `RelativeSectionComparison`: the public comparison API whose hypotheses use
  only `RelativePrimitiveSectionData` and the standard model facts.  It gives
  both representative formulas, the two inverse identities, the linear
  equivalence, and independence from every choice of relative sections.
- `CoordinateOrderIndependence`: the descended forward comparison map (2.35)
  and the resulting linear equivalence are independent of the coordinate
  order.  The proof identifies them as inverses of the same order-free reverse
  map, rather than comparing two ordered paths cell by cell.
- `PrimitiveQuotientFunctoriality`: the abstract strict contravariance in
  (2.36): compatible morphisms of facet-restriction data preserve `Zprim` and
  `Bprim`, induce maps on `TPrime`, respect identity and composition on the
  nose, and are independent of the facet witnesses once the global primitive
  pullback is fixed.
- `FiniteSimplicialCochain`, `SimplicialFacetData`,
  `SimplicialCoboundarySquare`, and `SimplicialConeContraction`: the actual
  finite ordered simplicial cochain complex, literal simplex restrictions,
  `d² = 0`, and the positive- and zero-degree cone contraction identities on
  closed stars.
- `SimplicialRelativePrimitive`, `SimplicialRelativePrimitiveZero`, and their
  two data-packaging modules: the explicit closed-star correction in
  (2.22)--(2.24), including the degree-zero global-constant correction and its
  facetwise compatibility.
- `SimplicialPhysicalPrimitiveComparison`: the concrete degree-uniform
  equivalence `T(M) ≃ T'(M)` for finite ordered simplicial cochains, together
  with the representative formulas (2.34) and (2.35).
- `SimplicialCochainPullback`: strict concrete contravariance for
  order-embedding simplicial maps; the abstract functoriality module remains
  the order-free interface used by the comparison proof.
- `Section3ConeOperatorReplacement`: the uniform formula
  `bottom(t) = h(d t)`, its equality of coboundaries with `t`, vanishing on
  apex coordinates, and the support-nonincreasing carrier statement for an
  elementary apex cochain.
- `EllDistribution` and `Section3SquareStripLocality`: linearization of the
  one-edge-minus-word error over base distributions, its compatibility with
  iterated finite differences, and the proof that every elementary local cube
  is sent to the full physical identity denominator by the square-strip
  calculation.
- `Section3SimplexLocalTau` and `Section3SimplicialLocalTau`: the elementary
  cube refinement of simplex-local `tau`, its compatible carrier primitive
  sections, and the uniform positive- and zero-degree vanishing theorem.
- `ElementaryPathCoefficientDecomposition`, `Section3LocalCubeReplacement`,
  and `Section3SimultaneousReplacement`: finite complete-label coefficient
  reconstruction, the local-cube replacement error, and simultaneous
  replacement of every apex label modulo `E_id`.
- `Section3ApexFreeCoboundary`, `Section3BottomOperators`, and
  `Section3SimplicialBottomOperators`: the isomorphism between apex-free
  cochains and cone coboundaries, the bottom path lift, boundary injectivity,
  and the conclusion that every invariant path using only bottom operators is
  an identity.  All statements include cochain degree zero.
- `Section3PathFacetRefinement` and `Section3CarrierTauGlobal`: passage between
  the apex-containing carrier family and the global simplicial facet family,
  including the global theorem `tau(C_v M) = 0`.
- `Section3ConeVanishing`: the final representative inclusion
  `E_inv <= E_id`, quotient vanishing `T = 0`, and transport through the
  Section 2 equivalence to `T' = 0` under the intrinsic `IsConeAt` condition.
- `Section3SimplicialConeModel` and `Section3LiteralConeVanishing`: a literal
  cone on `Option V` with `none` as apex and `some` as the bottom embedding,
  followed by direct, user-facing statements of
  `tau(C_v M) = T(C_v M) = T'(C_v M) = 0`.
- `SimplicialMaximalFacetPresentation`: finite maximal-facet extension,
  nested primitive and physical restriction factorization, and literal
  equality of the all-simplex and maximal-facet presentations of `E_inv`,
  `E_id`, `Zprim`, `Bprim`, `D_inv`, and `D_id`.  This closes the notational
  gap between the paper's maximal facets and the redundant all-simplex Lean
  presentation.
- `Section4DoldKanModels`, `Section4DoldKanHomology`,
  `Section4DoldKanCochainBridge`, `Section4DoldKanExplicitBridge`,
  `Section4NormalizedCochainBridge`, and `Section4CochainMapNaturality`: the
  standard models are actual Mathlib
  Dold--Kan objects: `K(G,q)` is obtained from `G[q]`, `L(G,q)` from the
  two-term identity complex, and `d : L → K` from the disk projection.  The
  disk complex has an explicit contraction `dh+hd=1`; normalized `L` is
  acyclic, normalized `K` has `G` in degree `q` and zero elsewhere, and the
  degreewise Gamma summand formula for `d` is checked.  The explicit bridge
  also verifies the oriented-face incidence sign `(-1)^i` and the alternating
  coface formula.  The signed identification with normalized ordered-simplex
  cochains and its pullback naturality are complete for order-preserving
  simplicial embeddings.
- `Section4ReducedFreeFiber` and `Section4ReducedFreeSurjectivity`: the reduced
  free Abelian group construction is applied degreewise as a simplicial
  functor; `F(G,q)` is its categorical kernel, with the functor-category
  kernel identified degreewise with the concrete `ker (mapRedDist d)`.  For
  every paper degree `q >= 1`, the resulting sequence
  `0 -> F -> reducedFree L -> reducedFree K -> 0` is proved short exact.
- `Section4DoldKanDiskContraction`, `Section4DoldKanDiskExtraDegeneracy`,
  `Section4DoldKanDiskNativeContraction`, and
  `Section4ReducedFreeHomologyShift`: the standard Dold--Kan disk has an
  unconditional explicit contraction.  It survives the nonlinear
  reduced-free construction, makes the alternating-face complex acyclic,
  and gives the connecting isomorphism
  `H_n(F) ≅ H_(n+1)(reducedFree K)` from (4.5), exposed publicly as
  `standardFiberHomotopyReducedHomologyIso`.
- `Section4DegreeZeroRow`, `Section4BasedRow`, `Section4BasedDegreeZero`, and
  `Section4SimplicialBasepointLift`: the full algebraic degree-zero row
  (4.1)--(4.4), its based normalization, and both basepoint cases are checked.
  In cochain degree zero the lift is the actual global constant cochain; in
  positive cochain degrees the local basepoint group is proved trivial.
- `Section4FiberwiseExtension`, `Section4NormalizedPathFibers`,
  `Section4RelationPathExtension`, and `Section4BoundaryExtension`: the
  fiberwise relative relation lift of Lemma 4.2, the tensor-free finite-fiber
  replacement for (4.20), extension of relation paths, and naturality of
  their primitive boundaries are mechanically checked.  The increment lift
  is only a zero-preserving set map, exactly as required in the paper.
- `Section4CochainExtensionByZero` and
  `Section4RelativeCohomologyExtension`: relative cochains are the actual
  kernel of pullback, `H^(n+1)(Z,A;G)=0` is expressed as `range d = ker d`,
  and this equality directly constructs (4.7), the cocycle extension, (4.9),
  and the primitive-relation section.
- `Section4LiteralConeBoundaryHEP`,
  `Section4LiteralRelativeConeCriterionReverse`, and the three
  `Section4NativeConeCriterion*` modules: the cylinder--cone extension
  criterion is proved directly for Mathlib's native relative simplicial
  homotopies.  Together with the degree-zero row it identifies the primitive
  image with the actual subgroup of pointed-null maps.
- `Section4NativeTheta`: Proposition 4.3 and (4.14) are stated directly in
  genuine pointed simplicial homotopy classes as `nativeThetaOfReduced` and
  `nativeThetaOfReduced_obstruction`; the relative extension data are
  constructed internally from the displayed reduced-cohomology vanishing.
- `Section4ExactConsequences`, `Section4TopologicalComparisons`,
  `Section4Transgression`, and `Section4MainTheorems`: first-isomorphism,
  transgression, suspension, and sphere comparison compositions are checked
  once in a reusable generic layer.  `Section4MainTheorems` is retained as a
  legacy assembly API; its geometric arguments are explicit parameters, not
  axioms, and the native public endpoint below constructs them.
- `Section4SimplicialConeComparison`, `Section4SimplicialConeExtension`, and
  `Section4SimplicialTransgression`: bottom restriction is implemented on the
  literal cone.  Cone vanishing proves representative surjectivity in (4.18),
  and `T'(C_vX)=0` proves that a relatively zero algebraic extension is a
  boundary.  These files are the intermediate algebraic layer used by the
  unconditional native comparison.
- `Section4NativeTransgressionEquiv` and
  `Section4NativeTransgressionDegreeZero`: Proposition 4.5 is an equivalence
  with the genuine relative homotopy-class group.  Both paper degrees
  `q >= 2` and the endpoint `q = 1` are covered.  The latter proves directly
  that the apparent reduced-cohomology condition in degree `-1` is automatic
  for a nonempty complex.
- `Section4LiteralDoubleConeDifference` and
  `Section4LiteralDoubleConeDifferenceReverse`: the two-cone map (4.25) is an
  unconditional linear equivalence on native homotopy classes.  It is
  literally inner/lower cone minus other/upper cone, fixing the paper's sign.
- `Section4SuspensionCohomologyShift` and `Section4SuspensionDegreeZero`:
  reduced cohomology of the literal ordered suspension has the required shift;
  its degree-zero vanishing is proved directly from the cone edges.
- `Section4NativeMainTheorems`: the public objectwise endpoint for
  (4.24)--(4.27).  The types of its main comparisons contain only the complex,
  basepoint, degree, coefficient group, and the cohomology vanishings stated in
  the paper; no temporary `Input`, cycle-extension `E`, or lift `Q` escapes.

## Public Section 4 endpoint

| Paper | Native Lean declaration | Scope |
| --- | --- | --- |
| (4.5) | `standardFiberHomotopyReducedHomologyIso` | unconditional standard Dold--Kan models |
| (4.13)--(4.14) | `nativeThetaOfReduced`, `nativeThetaOfReduced_obstruction` | actual pointed mapping classes |
| (4.18), `q >= 2` | `canonicalNativeTransgressionLinearEquivOfReduced` | all extension choices internal |
| (4.18), `q = 1` | `canonicalNativeTransgressionLinearEquivDegreeZero` | assumes only reduced `H^0 = 0` |
| (4.24), `q >= 2` | `nativeLoopSuspensionEquivOfReduced` | cone-quotient presentation of the loop adjunction |
| (4.24), `q = 1` | `nativeLoopSuspensionEquivDegreeZero` | low endpoint included |
| (4.25) | `literalTwoConeDifferenceEquiv` | unconditional, with the stated sign |
| (4.26), `q >= 2` | `nativeSuspensionEquivOfReduced` | literal composite `theta^(-1) delta^(-1) Tr` |
| (4.26), `q = 1` | `nativeSuspensionEquivDegreeZero` | low endpoint included |
| (4.27) | `nativeSphereTauPiPresentationOfReduced`, the two `nativeSphereTPrimeLoopPiPresentation*` declarations, and the two `standardSphere*PiHomologyIso` declarations | native mapping-class and Dold--Kan arrows; the oriented-sphere evaluation between them is the standard outer identification |

Every theorem in the formal modules is proved without `sorry`, `admit`, or
additional axioms.

## Scope boundary

The objectwise theorems of Sections 2--4, through the suspension comparison
(4.26), are mechanically complete in every paper degree `q >= 1`.

Two standard outer layers are intentionally not re-developed here.  First,
(4.24) uses the cone quotient `[C_vX/X,A]_*` as the standard presentation of
`[X, Omega A]_*`.  Second, (4.27) reads the mapping classes of a chosen
oriented simplicial `d`-sphere as `pi_d`; the project supplies the native
mapping-class arrows and the unconditional Dold--Kan homotopy--homology arrows
without inventing a placeholder equivalence between them.  This agrees with
the manuscript's use of the oriented-sphere identification as a definition.

The current concrete functoriality scope is smaller than the manuscript's
unqualified word "natural".  Ordered cochain pullback and its Dold--Kan
compatibility are implemented for order-preserving injective vertex maps.
Maps with degeneracies would require the usual zero-on-degenerate and signed
sorting branches.  Moreover, the final naturality squares for `theta` and
`Tr` have not been packaged even in the embedding-only scope, although their
representative formulas and the necessary pullback components are proved.
This is a functoriality/general-source-map limitation, not a missing step in
the objectwise isomorphisms above.

## Build

From this directory, run:

```powershell
lake build
```

The pinned toolchain is recorded in `lean-toolchain`; Lake fetches the matching
Mathlib revision from `lakefile.toml`.
