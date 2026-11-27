import Formalization.Transport.Strictification
import Formalization.Transport.SourceIndependence
import Formalization.Transport.IntegralPrism
import Formalization.Transport.FundamentalEvaluation
import Formalization.Transport.TriangulatedSphere

/-!
# Transport multiplication on a triangulated vacuum orbit

The entry point for the algebraic classification is
`GeneralSphereT.Transport.simplicialPrimitiveClassification`. Its source
uses only top-dimensional simplices for both locality and rephasing.
Its target is the character group of the strict primitive quotient used by
the existing sphere library. The comparison constructs both directions.

`simplicialFiniteSeparatingWords` gives the simultaneous finite family
of signed words. `finite_statistics_on_vacuum_orbit` proves that the same
family gives scalar phases and separates classes at any chosen source. `strictification_iff_class_zero` detects a single local
rephasing by the value of the classification equivalence.

`Prism.physicalPrism` is the oriented triangle integral at an exact
physical configuration. `Prism.physicalPrism_assoc` is its tetrahedron
identity and `Prism.physicalPrism_of_coboundary` computes its value on a
coboundary using the actual segment integral. `Prism.physicalPrismMultiplier`
proves the normalized locality, associativity and closed hopping axioms for this
formula. `Prism.prismClass` descends it to normalized EM cohomology using one
simultaneous normalized facet rephasing.

`Prism.integralPrism` sends actual integral processes to normalized EM cycle
classes. `Prism.prism_pairing` verifies the representative pairing including
its sign. `Prism.prism_bijective_iff_integral` reduces bijectivity to that of
this specified integral map. `fundamentalEvaluation_mk` computes evaluation
for degreewise projective chain complexes with an oriented homology generator.

`Prism.witness_measures` computes the triangle character using the projection
of a specified disk chain. `Prism.coneWitness_boundary` identifies its integral
boundary with the native transgression on the signed relative cone cycle.
`RelativeChains.altEvaluation_mk` computes the native evaluation isomorphism
on the fundamental cycle. `Prism.orientedTriangleIso` is the additive equivalence
for a pure oriented integral homology sphere in the admissible degrees, and
`Prism.orientedTriangleIso_mk` computes it by the signed triangle formula.
`Prism.reducedExact_of_orientation` deduces lower cohomology vanishing with
arbitrary coefficients from the single integral relative fundamental class.

`Prism.triangulatedSphereTriangleIso` starts with a homeomorphism of the
geometric realization to the Euclidean sphere and the signed top simplices.
`Prism.triangulatedSphereTriangleIso_representative` identifies the actual
multiplier on every triple of inputs. `Prism.triangulatedSphereIntegralIso`
is the corresponding equivalence on integral processes.
-/

