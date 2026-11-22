# Two Infinite Families of Base-6 Lychrel Numbers

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
Full companion write-up: <https://mathdiscoveries.org/results/lychrel-base-6-families.html>.
