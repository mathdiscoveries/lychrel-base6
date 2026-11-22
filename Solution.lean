module

public import LychrelBase6

/-!
# Base-6 Lychrel Numbers: Proved Solution (`Solution`)

Discharges every headline theorem of `Challenge.lean` from the unconditional carry-automaton
formalization in `LychrelBase6`, using only Lean's standard axioms (`propext`, `Quot.sound`,
`Classical.choice`).
-/

@[expose] public section

namespace LychrelBase6

/-- Most-significant-digit-first base-6 expansion of Family 1 (`110 + 2m` digits). -/
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

/-- Most-significant-digit-first base-6 expansion of Family 2 (`108 + 2m` digits). -/
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

private theorem xValue_eq_xFam (m : ℕ) : xValue m = xFam m := rfl

private theorem yValue_eq_yFam (m : ℕ) : yValue m = yFam m := rfl

theorem xValue_lychrel : ∀ m : ℕ, IsLychrel6 (xValue m) :=
  xFam_lychrel

theorem xValue_step12 : ∀ m : ℕ, revAdd6^[12] (xValue m) = xValue (m + 3) :=
  xFam_step12

theorem xValue_strictMono : StrictMono xValue :=
  xFam_strictMono

theorem xValue_zero_eq :
    xValue 0 =
      10597199767879923759424316990930862796672101123713351165673551415976972661719017382131 :=
  xFam_zero_eq

theorem yValue_lychrel : ∀ m : ℕ, IsLychrel6 (yValue m) :=
  yFam_lychrel

theorem yValue_step12 : ∀ m : ℕ, revAdd6^[12] (yValue m) = yValue (m + 3) :=
  yFam_step12

theorem yValue_strictMono : StrictMono yValue :=
  yFam_strictMono

theorem yValue_zero_eq :
    yValue 0 =
      293400065643122906317218502532643307621072769521307830691373332756338351497087823275 :=
  yFam_zero_eq

theorem xValue_disjoint_yValue : ∀ m n : ℕ, xValue m ≠ yValue n :=
  xFam_disjoint_yFam

end LychrelBase6
