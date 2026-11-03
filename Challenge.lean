module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.Geometry.Manifold.ContMDiff.Defs
public import Mathlib.Geometry.Manifold.MFDeriv.Defs
public import Mathlib.Geometry.Manifold.Notation

/-!
# Smale's sphere eversion theorem

This file is the statement of record for the Palomar entry of the sphere eversion project.
It imports only Mathlib. The proof is in `Solution.lean`, which imports the project.

## The theorem

`Smale` states that the unit sphere `𝕊²` in Euclidean `ℝ³` can be turned inside out through
immersions: there is a family of maps `f t : 𝕊² → ℝ³`, indexed by `t : ℝ`, such that

* `(t, x) ↦ f t x` is `C^∞` on the product manifold `ℝ × 𝕊²`;
* `f 0` is the inclusion `x ↦ x`;
* `f 1` is the antipodal map `x ↦ -x`;
* every `f t` is a `C^∞` immersion, i.e. its differential is injective at every point.

The restriction of `f` to `t ∈ [0, 1]` is therefore a regular homotopy from the standard
embedding of the sphere to the antipodal embedding, whose outward normal is the inward normal of
the standard one. This is the special case, for these two immersions, of Smale's theorem that
any two immersions of `S²` in `ℝ³` are regularly homotopic (S. Smale, *A classification of
immersions of the two-sphere*, Trans. Amer. Math. Soc. 90 (1959) 281–290).

## How the statement is expressed in Lean

* `ℝ³` is `EuclideanSpace ℝ (Fin 3)` and `𝕊²` is Mathlib's `Metric.sphere (0 : ℝ³) 1`, with
  Mathlib's smooth manifold structure given by stereographic charts modelled on `𝓡 2`
  (`EuclideanSpace ℝ (Fin 2)`, a manifold without boundary).
* `↿f : ℝ × 𝕊² → ℝ³` is the uncurried family; `𝓘(ℝ, ℝ).prod (𝓡 2)` is the product model, so the
  first conjunct is joint smoothness in the time parameter and the point of the sphere.
* `∞` is smoothness of class `C^∞` (not analyticity).
* `Immersion` is defined below, copied verbatim from the project: a `C^n` map whose manifold
  derivative `mfderiv` is injective at every point. Mathlib's `mfderiv` takes the junk value `0`
  at points of non-differentiability, but the `contMDiff` field rules this case out, so the
  injectivity condition is about the genuine differential. In finite dimensions this is the usual
  notion of immersion. The intermediate maps are *not* required to be injective; an eversion
  through embeddings is impossible.
* The parameter `t` ranges over all of `ℝ`, not only `[0, 1]`; this is at least as strong as
  the statement on `[0, 1]`.

No hypothesis is added to Smale's statement, and the only axioms used are `propext`,
`Quot.sound` and `Classical.choice`.

## What is not covered here

The project also proves Gromov's h-principle for open and ample first-order differential
relations between manifolds (theorem `Gromov` in `SphereEversion/Main.lean`), of which this is a
corollary. That general theorem is not part of this Challenge and is not checked by this
Comparator configuration. The Challenge does not state Smale's full classification of immersions
of `S²` up to regular homotopy.

## Proof account

The Lean proof does not follow Smale's original argument. It follows Gromov's h-principle,
proved by convex integration in the form of M. Theillière (*Convex integration theory without
integration*, arXiv:1909.04908), as described in P. Massot, F. van Doorn and O. Nash,
*Formalising the h-principle and sphere eversion* (CPP 2023, arXiv:2210.07746):

1. The relation "the 1-jet has injective linear part" (immersions) between manifolds of
   dimensions `2 < 3` is open and ample (`immersionRel_open_ample`).
2. A *formal eversion* is built explicitly (`formalEversion`): its base map is the straight-line
   homotopy `(1 - s) • x + s • (-x)` with `s` a smooth step function of `t`, and its linear part is
   the derivative of the inclusion composed with a rotation by angle `π s` about the axis `x`.
   It is a family of formal solutions, and it is holonomic for `t < 1/4` and `t > 3/4`.
3. The parametric, relative h-principle for open and ample relations
   (`immersionRel_satisfiesHPrincipleWith`, applied with parameter space `ℝ` and closed set
   `{0, 1} × 𝕊²`) deforms it to a family of genuine immersions, unchanged near `t = 0` and
   `t = 1`, which gives `f`.
-/

open Metric Set Function

open scoped Manifold ContDiff

/-- `ℝ³`, Euclidean 3-space. -/
notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `𝕊²`, the unit sphere in `ℝ³`. -/
notation "𝕊²" => sphere (0 : ℝ³) 1

public section

noncomputable section

-- The block below is copied verbatim from the project file
-- `SphereEversion/ToMathlib/Geometry/Manifold/Immersion.lean`; Comparator requires the
-- definition to be identical in the Challenge and Solution environments.
section ImmersionDefinition

open Set Function

open scoped Manifold ContDiff

-- Let `M` be a manifold with corners over the pair `(E, H)`.
-- Let `M'` be a manifold with corners over the pair `(E', H')`.
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [instE : NormedAddCommGroup E] [instE' : NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']

/-- `Immersion I I' f n` says that `f : M → M'` is a `C^n` immersion between the manifolds `M`
(modelled by `I`) and `M'` (modelled by `I'`): `f` is `C^n` (field `contMDiff`), and its manifold
derivative `mfderiv I I' f p : T_p M →L T_{f p} M'` is injective at every point `p`
(field `diff_injective`). -/
structure Immersion (f : M → M') (n : WithTop ℕ∞) : Prop where
  contMDiff : CMDiff n f
  diff_injective : ∀ p, Injective (mfderiv% f p)

end ImmersionDefinition

end

end

/-- **Smale's sphere eversion theorem.** There is a family `f t : 𝕊² → ℝ³`, `t ∈ ℝ`, which is
jointly `C^∞` in `(t, x)`, starts at the inclusion of the sphere (`t = 0`), ends at the antipodal
map `x ↦ -x` (`t = 1`), and such that every `f t` is a `C^∞` immersion. -/
public theorem Smale :
    ∃ f : ℝ → 𝕊² → ℝ³,
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ³) ∞ ↿f ∧
    (f 0 = fun x : 𝕊² ↦ (x : ℝ³)) ∧
    (f 1 = fun x : 𝕊² ↦ -(x : ℝ³)) ∧
    ∀ t, Immersion (𝓡 2) 𝓘(ℝ, ℝ³) (f t) ∞ := by
  sorry
