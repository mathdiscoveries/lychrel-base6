module

public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Monotone.Basic

/-!
# Base-6 Lychrel Numbers: Statement Surface (`Challenge`)

Two explicit, strictly increasing, pairwise disjoint infinite families `xValue m` and `yValue m`
of natural numbers (`m : ℕ`) that never reach a base-6 palindrome under repeated base-6
reverse-and-add `T(n) = n + rev₆(n)`. Each family satisfies the exact period-12 self-similar
recurrence `T^[12](xValue m) = xValue (m + 3)` and `T^[12](yValue m) = yValue (m + 3)`, with
base-6 lengths `110 + 2m` and `108 + 2m` respectively.
-/

@[expose] public section

namespace LychrelBase6

/-- Base-6 digit reversal of a natural number `n`.
Since `Nat.digits 6 n` is least-significant-digit-first, `(Nat.digits 6 n).reverse` places
the most-significant digit at the units position, so `Nat.ofDigits 6 (Nat.digits 6 n).reverse`
evaluates the reversed base-6 digit string. -/
def rev6 (n : ℕ) : ℕ :=
  Nat.ofDigits 6 (Nat.digits 6 n).reverse

/-- One base-6 reverse-and-add step: `T(n) = n + rev6 n`. -/
def revAdd6 (n : ℕ) : ℕ :=
  n + rev6 n

/-- A natural number `n` is a base-6 palindrome iff its canonical base-6 digit list equals
its own reversal. -/
def IsPalindrome6 (n : ℕ) : Prop :=
  (Nat.digits 6 n).reverse = Nat.digits 6 n

/-- A natural number `n` is a base-6 Lychrel number if no iterate `revAdd6^[j] n` (`j ≥ 0`)
is a base-6 palindrome. -/
def IsLychrel6 (n : ℕ) : Prop :=
  ∀ j : ℕ, ¬ IsPalindrome6 (revAdd6^[j] n)

/-- Most-significant-digit-first base-6 expansion of Family 1 (`110 + 2m` digits):
`133535 ++ 5^m ++ M₁ ++ 0^m ++ 003443`. -/
def xDigits (m : ℕ) : List ℕ :=
  [1, 3, 3, 5, 3, 5] ++ List.replicate m 5 ++
    [5, 1, 2, 0, 5, 3, 3, 3, 3, 1, 1, 1, 4, 0, 1, 2, 0, 3, 1, 4, 0, 2, 3, 3, 3, 3, 4, 5, 5, 0,
     3, 3, 4, 5, 4, 4, 4, 5, 0, 4, 5, 1, 1, 1, 1, 4, 3, 0, 3, 0, 3, 0, 3, 4, 0, 2, 1, 0, 5, 4,
     1, 0, 4, 3, 5, 0, 4, 2, 4, 1, 5, 5, 3, 3, 4, 3, 3, 1, 5, 4, 1, 3, 1, 1, 1, 0, 3, 2, 2, 1,
     3, 3, 3, 3, 5, 0, 1, 1] ++
    List.replicate m 0 ++ [0, 0, 3, 4, 4, 3]

/-- Natural-number value of Family 1 at index `m : ℕ`. -/
def xValue (m : ℕ) : ℕ :=
  Nat.ofDigits 6 (xDigits m).reverse

/-- Most-significant-digit-first base-6 expansion of Family 2 (`108 + 2m` digits):
`13343 ++ 0^m ++ M₂ ++ 5^m ++ 52443`, where `M₂` is the base-6 digit complement `d ↦ 5 - d`
of `M₁`. -/
def yDigits (m : ℕ) : List ℕ :=
  [1, 3, 3, 4, 3] ++ List.replicate m 0 ++
    [0, 4, 3, 5, 0, 2, 2, 2, 2, 4, 4, 4, 1, 5, 4, 3, 5, 2, 4, 1, 5, 3, 2, 2, 2, 2, 1, 0, 0, 5,
     2, 2, 1, 0, 1, 1, 1, 0, 5, 1, 0, 4, 4, 4, 4, 1, 2, 5, 2, 5, 2, 5, 2, 1, 5, 3, 4, 5, 0, 1,
     4, 5, 1, 2, 0, 5, 1, 3, 1, 4, 0, 0, 2, 2, 1, 2, 2, 4, 0, 1, 4, 2, 4, 4, 4, 5, 2, 3, 3, 4,
     2, 2, 2, 2, 0, 5, 4, 4] ++
    List.replicate m 5 ++ [5, 2, 4, 4, 3]

/-- Natural-number value of Family 2 at index `m : ℕ`. -/
def yValue (m : ℕ) : ℕ :=
  Nat.ofDigits 6 (yDigits m).reverse

/-- There are infinitely many base-6 Lychrel numbers. -/
theorem infinite_lychrel6 : Set.Infinite {n : ℕ | IsLychrel6 n} := by
  sorry

/-- Every member of Family 1 is a base-6 Lychrel number. -/
theorem xValue_lychrel : ∀ m : ℕ, IsLychrel6 (xValue m) := by
  sorry

/-- Family 1 satisfies the exact 12-step self-similar recurrence `T^[12](x(m)) = x(m + 3)`. -/
theorem xValue_step12 : ∀ m : ℕ, revAdd6^[12] (xValue m) = xValue (m + 3) := by
  sorry

/-- Family 1 is strictly increasing. -/
theorem xValue_strictMono : StrictMono xValue := by
  sorry

/-- Exact base-10 value of the smallest Family 1 member `x(0)` (86 decimal digits). -/
theorem xValue_zero_eq :
    xValue 0 =
      10597199767879923759424316990930862796672101123713351165673551415976972661719017382131 := by
  sorry

/-- Every member of Family 2 is a base-6 Lychrel number. -/
theorem yValue_lychrel : ∀ m : ℕ, IsLychrel6 (yValue m) := by
  sorry

/-- Family 2 satisfies the exact 12-step self-similar recurrence `T^[12](y(m)) = y(m + 3)`. -/
theorem yValue_step12 : ∀ m : ℕ, revAdd6^[12] (yValue m) = yValue (m + 3) := by
  sorry

/-- Family 2 is strictly increasing. -/
theorem yValue_strictMono : StrictMono yValue := by
  sorry

/-- Exact base-10 value of the smallest Family 2 member `y(0)` (84 decimal digits). -/
theorem yValue_zero_eq :
    yValue 0 =
      293400065643122906317218502532643307621072769521307830691373332756338351497087823275 := by
  sorry

/-- The two infinite families are pairwise disjoint (`x(m) ≠ y(n)` for all `m, n`). -/
theorem xValue_disjoint_yValue : ∀ m n : ℕ, xValue m ≠ yValue n := by
  sorry

end LychrelBase6
