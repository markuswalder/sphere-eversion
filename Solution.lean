module

public import SphereEversion.Global.Immersion

/-!
# Solution: Smale's sphere eversion theorem

This module proves the statement `Smale` of `Challenge.lean` from the sphere eversion project.
The statement is identical to the one in `Challenge.lean`, and to the theorem `Smale` in
`SphereEversion/Main.lean`; this file imports `SphereEversion.Global.Immersion` rather than
`SphereEversion.Main` so that the name `Smale` is not declared twice.

The proof applies `sphere_eversion` (in `SphereEversion/Global/Immersion.lean`), which proves
the result for any three-dimensional real inner product space `E` in place of `ℝ³`, to
`E = ℝ³`. That theorem is obtained from the parametric h-principle for the open and ample
relation of immersions (`immersionRel_satisfiesHPrincipleWith`) applied to an explicit formal
eversion (`formalEversion`).
-/

open Metric Set Function

open scoped Manifold ContDiff

/-- `ℝ³`, Euclidean 3-space. -/
notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- `𝕊²`, the unit sphere in `ℝ³`. -/
notation "𝕊²" => sphere (0 : ℝ³) 1

/-- **Smale's sphere eversion theorem.** There is a family `f t : 𝕊² → ℝ³`, `t ∈ ℝ`, which is
jointly `C^∞` in `(t, x)`, starts at the inclusion of the sphere (`t = 0`), ends at the antipodal
map `x ↦ -x` (`t = 1`), and such that every `f t` is a `C^∞` immersion. -/
public theorem Smale :
    ∃ f : ℝ → 𝕊² → ℝ³,
    ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ³) ∞ ↿f ∧
    (f 0 = fun x : 𝕊² ↦ (x : ℝ³)) ∧
    (f 1 = fun x : 𝕊² ↦ -(x : ℝ³)) ∧
    ∀ t, Immersion (𝓡 2) 𝓘(ℝ, ℝ³) (f t) ∞ :=
  sphere_eversion ℝ³
