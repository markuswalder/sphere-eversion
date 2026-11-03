# The sphere eversion project

This project formalizes the proof of a theorem implying the existence of sphere
eversions. It was carried out by Patrick Massot, Floris van Doorn and Oliver
Nash, with crucial help from the wider Lean community. The proof of the main theorem was completed on November 12th 2022.
Details can be found on the [project website.](https://leanprover-community.github.io/sphere-eversion/)

This project originally used Lean 3 but was ported to Lean 4 with crucial help from Yury Kudryashov.

# Statement checked for the Palomar registry

[`Challenge.lean`](Challenge.lean) states Smale's sphere eversion theorem using Mathlib only:
there is a family of maps `f t` from the unit sphere `𝕊²` of `ℝ³` to `ℝ³`, indexed by
`t : ℝ` and jointly smooth in `(t, x)`, with `f 0` the inclusion, `f 1` the antipodal map
`x ↦ -x`, and every `f t` a smooth immersion (a smooth map with injective differential at
every point). [`Solution.lean`](Solution.lean) proves it from this project, and
[`comparator.json`](comparator.json) tells
[Comparator](https://github.com/leanprover/comparator) to check that the two statements agree
and that the proof uses only the axioms `propext`, `Quot.sound` and `Classical.choice`.

The Challenge covers only the eversion statement (theorem `Smale` in `SphereEversion/Main.lean`),
not Gromov's general h-principle (theorem `Gromov` in the same file) and not Smale's full
classification of immersions of the sphere. Provenance, sources and limitations are recorded in
[`formalization.yaml`](formalization.yaml); submissions go to
<https://submit.palomar-registry.org/>.

# Build the Lean files

To build the Lean files of this project, you need to have a working version of Lean.
See [the installation instructions](https://leanprover-community.github.io/get_started.html) (under Regular install).

To build the project, run `lake exe cache get` and then `lake build`.

# Build the blueprint

To build the web version of the blueprint, you need a working LaTeX installation.
Furthermore, you need some packages:
```
sudo apt install graphviz libgraphviz-dev
pip3 install invoke pandoc
cd .. # go to folder where you are happy clone git repos
git clone git@github.com:plastex/plastex
pip3 install ./plastex
git clone git@github.com:PatrickMassot/leanblueprint
pip3 install ./leanblueprint
cd sphere-eversion
```

To actually build the blueprint, run
```
lake exe cache get
lake build
inv all
```

To view the web-version of the blueprint locally, run `inv serve` and navigate to
`http://localhost:8000/` in your favorite browser.
