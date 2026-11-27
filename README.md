# Two Infinite Families of Base-6 Lychrel Numbers

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.24490763.svg)](https://doi.org/10.5281/zenodo.24490763)

Unconditional Lean 4 (`v4.35.0`) formalization of two explicit, strictly
increasing, pairwise disjoint infinite families of base-6 Lychrel numbers
under repeated base-6 reverse-and-add $T(n) = n + \operatorname{rev}_6(n)$.

## Main results (`Challenge.lean`)

- `LychrelBase6.infinite_lychrel6`: infinitely many base-6 Lychrel numbers exist.
- `LychrelBase6.xValue_lychrel`, `xValue_step12`, `xValue_strictMono`, `xValue_zero_eq`:
  Family 1 ($110 + 2m$ base-6 digits, smallest member $x(0)$ with 86 decimal digits)
  satisfies $T^{12}(x(m)) = x(m + 3)$ and never hits a base-6 palindrome.
- `LychrelBase6.yValue_lychrel`, `yValue_step12`, `yValue_strictMono`, `yValue_zero_eq`:
  Family 2 ($108 + 2m$ base-6 digits, smallest member $y(0)$ with 84 decimal digits)
  satisfies $T^{12}(y(m)) = y(m + 3)$ and never hits a base-6 palindrome.
- `LychrelBase6.xValue_disjoint_yValue`: $x(m) \neq y(n)$ for all $m, n \in \mathbb{N}$.

## Verification

```sh
lake exe cache get
lake build
lake env lean LychrelBase6/Verify.lean
```

Every theorem uses only Lean's standard axioms (`propext`, `Quot.sound`,
`Classical.choice`), with zero `sorry` and zero `native_decide`.

Prepared for submission to the [Palomar Registry](https://submit.palomar-registry.org/).
Companion paper, which states and proves every compared statement: <https://mathdiscoveries.org/results/lychrel-base-6-families>.

Coverage by this package's Palomar comparison: of the companion paper's 10 main results, 2 are compared in Lean in full (20%; Theorems 1 and 2) and 2 in part (Corollary 3: every $x(m)$ and $y(m)$ is a base-6 Lychrel number, without its positivity and per-iterate form; Theorem 7: the two families are disjoint, without the injectivity of all six forward trajectories). Five more (Lemma 4, Theorem 5, Proposition 6, Theorem 8 and Corollary 9) are proved in this package's Lean library but not compared, though the compared statements include the infinitude of base-6 Lychrel numbers; Proposition 10 is by certificate only; Conjecture 11 is open and not counted.

AI research agents built and directed by Tyler B. Hughes generated and checked this work. No human mathematician has yet refereed the proof.
