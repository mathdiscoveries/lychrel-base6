module

public import LychrelBase6.CarryEngine

import Mathlib.Tactic

/-!
# Two Infinite Families of Base-6 Lychrel Numbers (`xFam` and `yFam`)

Unconditional formalization of `tworun-1.md` §3.2 and §3.3:
- **Family 1 (`xFam m`)**: signal `010101010101`, overflow pattern `010101010101`,
  `110 + 2m` base-6 digits (`A₁ = 133535`, `h₁ = 5`, `|M₁| = 98`, `l₁ = 0`, `Z₁ = 003443`).
- **Family 2 (`yFam m`)**: signal `101010101010`, overflow pattern `010101010101`,
  `108 + 2m` base-6 digits (`A₂ = 13343`, `h₂ = 0`, `|M₂| = 98`, `l₂ = 5`, `Z₂ = 52443`),
  where `M₂` is the base-6 digit complement `d ↦ 5 - d` of `M₁`.

For EVERY `m ≥ 0`, combining the 12-step symbolic carry automaton (Lemma S + Lemma C) for
`m ≥ 6` with exact kernel-checked digit-list arithmetic for `m ∈ {0, 1, 2, 3, 4, 5}`, we
prove unconditionally:
1. `revAdd6^[12] (xFam m) = xFam (m + 3)` and `revAdd6^[12] (yFam m) = yFam (m + 3)`.
2. No intermediate step `t < 12` is a base-6 palindrome.
3. Every `xFam m` and every `yFam m` is a base-6 Lychrel number (`IsLychrel6`).
4. Both families are strictly increasing (`StrictMono`) and pairwise disjoint
   (`∀ m n, xFam m ≠ yFam n`), differing already at the 4th base-6 digit (`5 ≠ 4`).
5. Exact base-10 values of the smallest members `xFam 0` (86 digits) and `yFam 0` (84 digits).
-/

@[expose] public section

namespace LychrelBase6

set_option maxRecDepth 4096

/-- Shared 12-step alternating overflow pattern `010101010101`. -/
def overflowPattern12 : List Bool :=
  [false, true, false, true, false, true, false, true, false, true, false, true]

/-- Helper bound: every proper prefix of `overflowPattern12` contains at most 5 `true` entries. -/
theorem overflowPattern12_prefix_count (t : ℕ) (ht : t < overflowPattern12.length) :
    (overflowPattern12.take t).count true + 1 ≤ 6 := by
  have ht' : t < 12 := ht
  interval_cases t <;> decide

/-- Regrouped target form after 12 steps (`p = 6` absorbed into outer blocks, `q = 3` into middle). -/
def regroupTarget63 (F : Form) : Form where
  A := F.A ++ List.replicate 6 F.h
  h := F.h
  M := List.replicate 3 F.h ++ F.M ++ List.replicate 3 F.l
  l := F.l
  Z := List.replicate 6 F.l ++ F.Z

/-! ### Family 1: `x(m)` (signal `010101010101`) -/

/-- Exact base-6 template of Family 1 (`tworun-1.md` §3.2). -/
def xForm0 : Form where
  A := [1, 3, 3, 5, 3, 5]
  h := 5
  M := [5, 1, 2, 0, 5, 3, 3, 3, 3, 1, 1, 1, 4, 0, 1, 2, 0, 3, 1, 4, 0, 2, 3, 3, 3, 3, 4, 5, 5, 0,
        3, 3, 4, 5, 4, 4, 4, 5, 0, 4, 5, 1, 1, 1, 1, 4, 3, 0, 3, 0, 3, 0, 3, 4, 0, 2, 1, 0, 5, 4,
        1, 0, 4, 3, 5, 0, 4, 2, 4, 1, 5, 5, 3, 3, 4, 3, 3, 1, 5, 4, 1, 3, 1, 1, 1, 0, 3, 2, 2, 1,
        3, 3, 3, 3, 5, 0, 1, 1]
  l := 0
  Z := [0, 0, 3, 4, 4, 3]

/-- Family 1 (`x(m)` for `m ≥ 0`), having `110 + 2m` base-6 digits. -/
def xFam (m : ℕ) : ℕ :=
  formVal xForm0 m

theorem xForm0_valid : ValidForm xForm0 :=
  validForm_of_bool (by decide)

theorem xFam_digits_length (m : ℕ) : (evalForm xForm0 m).length = 110 + 2 * m := by
  rw [evalForm_length]
  rfl

/-- Exact 12-row symbolic orbit of Family 1 (`tworun-1.md` §3.2), paired with its overflow bits
`010101010101`. -/
def xChain : List (Bool × Form) :=
  [ (false, ⟨[5, 2, 2, 2, 4, 0], 0,
      [0, 2, 3, 0, 3, 1, 1, 0, 4, 3, 3, 4, 4, 1, 2, 3, 3, 5, 0, 3, 2, 0, 1, 2, 1, 1, 4, 5, 0, 5,
       0, 1, 5, 5, 2, 2, 5, 0, 5, 3, 5, 2, 3, 2, 0, 1, 3, 3, 3, 3, 3, 4, 1, 5, 1, 3, 3, 0, 3, 5,
       0, 5, 3, 2, 4, 5, 1, 5, 5, 1, 5, 4, 1, 1, 2, 0, 5, 2, 3, 5, 4, 3, 3, 2, 1, 4, 4, 3, 3, 5,
       1, 1, 1, 2, 5, 2, 3, 0],
      5, [5, 4, 3, 2, 1, 4]⟩),
    (true, ⟨[1, 3, 3, 5, 0, 2, 5], 5,
      [5, 0, 5, 5, 5, 5, 2, 2, 2, 4, 1, 1, 3, 2, 2, 5, 1, 1, 4, 0, 0, 4, 5, 1, 4, 2, 3, 3, 4, 2,
       4, 5, 3, 5, 3, 5, 0, 4, 1, 5, 1, 0, 0, 0, 3, 5, 3, 2, 1, 1, 1, 1, 1, 2, 5, 4, 1, 0, 0, 1,
       4, 1, 4, 5, 5, 4, 4, 3, 0, 4, 2, 5, 2, 2, 2, 4, 1, 5, 5, 1, 0, 4, 1, 0, 4, 3, 3, 3, 1, 1,
       3, 1, 2, 2, 5, 5, 5, 5, 1],
      0, [0, 0, 2, 5, 4, 4, 3]⟩),
    (false, ⟨[5, 2, 2, 4, 2, 3, 0], 0,
      [1, 0, 5, 5, 5, 1, 4, 3, 5, 5, 2, 5, 1, 0, 0, 5, 2, 5, 4, 2, 0, 4, 1, 0, 0, 5, 0, 3, 1, 0,
       5, 3, 2, 4, 3, 4, 5, 0, 0, 0, 1, 0, 1, 5, 3, 1, 4, 3, 2, 2, 2, 3, 5, 2, 2, 4, 1, 0, 2, 0,
       5, 5, 5, 5, 3, 4, 2, 2, 5, 1, 1, 2, 5, 5, 1, 0, 1, 3, 5, 1, 4, 5, 3, 0, 1, 0, 0, 4, 2, 5,
       5, 3, 5, 2, 5, 5, 5, 0, 0],
      5, [5, 2, 3, 5, 2, 1, 4]⟩),
    (true, ⟨[1, 3, 3, 5, 3, 5, 5, 5], 5,
      [5, 1, 1, 5, 5, 4, 4, 4, 1, 5, 4, 5, 3, 1, 0, 2, 0, 0, 5, 2, 4, 0, 1, 2, 0, 2, 4, 5, 5, 2,
       2, 4, 5, 5, 3, 1, 4, 4, 5, 5, 0, 3, 0, 3, 3, 5, 4, 4, 0, 4, 4, 5, 1, 3, 4, 0, 3, 2, 0, 3,
       1, 0, 0, 5, 4, 1, 2, 5, 0, 4, 1, 3, 0, 0, 4, 1, 0, 3, 1, 5, 4, 3, 4, 5, 5, 1, 0, 2, 3, 5,
       5, 5, 1, 3, 4, 5, 5, 4, 0, 2],
      0, [0, 0, 0, 0, 3, 4, 4, 3]⟩),
    (false, ⟨[5, 2, 2, 2, 4, 0, 0, 0], 0,
      [1, 2, 0, 5, 5, 3, 2, 0, 1, 5, 4, 2, 5, 1, 2, 1, 5, 5, 3, 1, 3, 1, 4, 2, 2, 0, 5, 0, 2, 4,
       0, 5, 5, 1, 5, 0, 3, 5, 0, 0, 3, 3, 3, 0, 4, 4, 2, 0, 0, 3, 3, 0, 0, 2, 3, 4, 0, 2, 3, 4,
       0, 5, 5, 3, 5, 5, 2, 4, 5, 0, 4, 2, 5, 5, 0, 1, 2, 4, 2, 4, 1, 2, 5, 0, 1, 1, 2, 0, 3, 4,
       5, 1, 0, 2, 3, 5, 4, 5, 2, 1],
      5, [5, 5, 5, 4, 3, 2, 1, 4]⟩),
    (true, ⟨[1, 3, 3, 5, 0, 2, 5, 5, 5], 5,
      [5, 2, 5, 0, 4, 5, 0, 4, 0, 3, 5, 2, 5, 5, 3, 3, 3, 0, 4, 5, 3, 1, 4, 2, 4, 3, 1, 4, 5, 5,
       2, 1, 5, 3, 4, 5, 0, 1, 4, 5, 1, 2, 0, 5, 1, 3, 1, 4, 0, 1, 1, 0, 0, 0, 5, 2, 2, 1, 0, 1,
       1, 1, 0, 5, 1, 0, 4, 4, 4, 4, 1, 2, 5, 0, 4, 0, 3, 5, 2, 4, 1, 3, 0, 4, 5, 2, 3, 4, 0, 0,
       3, 4, 2, 0, 5, 1, 5, 3, 5, 4, 3],
      0, [0, 0, 0, 0, 2, 5, 4, 4, 3]⟩),
    (false, ⟨[5, 2, 2, 4, 2, 3, 0, 0, 0], 0,
      [3, 1, 4, 4, 4, 0, 5, 4, 3, 2, 2, 3, 0, 4, 1, 0, 2, 4, 5, 2, 5, 0, 1, 2, 1, 3, 5, 5, 5, 1,
       4, 0, 4, 2, 2, 5, 2, 0, 5, 0, 2, 3, 1, 0, 4, 0, 0, 4, 0, 1, 2, 1, 0, 5, 0, 5, 4, 0, 0, 3,
       3, 0, 5, 0, 2, 0, 3, 2, 3, 5, 4, 2, 4, 4, 5, 4, 2, 2, 0, 5, 5, 2, 4, 5, 3, 0, 1, 3, 5, 3,
       3, 1, 2, 5, 0, 1, 3, 4, 5, 1, 2],
      5, [5, 5, 5, 2, 3, 5, 2, 1, 4]⟩),
    (true, ⟨[1, 3, 3, 5, 3, 5, 5, 5, 5, 5], 5,
      [5, 5, 3, 4, 3, 1, 2, 0, 3, 5, 4, 0, 1, 0, 1, 2, 1, 0, 4, 3, 5, 4, 5, 1, 4, 4, 2, 5, 4, 3,
       4, 3, 0, 1, 4, 5, 5, 4, 1, 4, 1, 0, 0, 1, 1, 2, 5, 1, 3, 0, 2, 4, 2, 1, 3, 1, 0, 2, 0, 2,
       0, 5, 1, 4, 0, 4, 5, 5, 5, 2, 0, 2, 4, 4, 4, 5, 1, 3, 4, 2, 0, 4, 5, 4, 3, 5, 0, 3, 2, 0,
       0, 5, 4, 0, 3, 5, 2, 2, 3, 3, 3, 0],
      0, [0, 0, 0, 0, 0, 0, 3, 4, 4, 3]⟩),
    (false, ⟨[5, 2, 2, 2, 4, 0, 0, 0, 0, 0], 0,
      [0, 3, 1, 1, 5, 4, 1, 3, 4, 4, 3, 0, 1, 2, 4, 3, 0, 4, 3, 3, 3, 5, 2, 0, 2, 0, 2, 4, 3, 2,
       0, 3, 3, 1, 4, 5, 3, 5, 0, 0, 0, 0, 2, 1, 3, 3, 0, 4, 4, 3, 1, 0, 2, 4, 5, 0, 2, 3, 1, 2,
       1, 0, 5, 5, 5, 4, 5, 4, 0, 2, 4, 1, 2, 3, 4, 2, 0, 2, 0, 1, 5, 4, 3, 2, 4, 0, 2, 4, 2, 1,
       1, 4, 3, 3, 4, 1, 4, 0, 2, 1, 2, 5],
      5, [5, 5, 5, 5, 5, 4, 3, 2, 1, 4]⟩),
    (true, ⟨[1, 3, 3, 5, 0, 2, 5, 5, 5, 5, 5], 5,
      [5, 5, 5, 2, 4, 0, 2, 3, 2, 2, 2, 1, 1, 2, 5, 2, 5, 1, 3, 0, 1, 2, 4, 3, 0, 4, 0, 5, 3, 0,
       4, 2, 1, 5, 2, 3, 5, 2, 4, 5, 5, 0, 1, 4, 3, 0, 5, 1, 4, 2, 5, 1, 2, 0, 3, 3, 1, 0, 0, 2,
       4, 1, 1, 0, 0, 5, 2, 5, 2, 2, 0, 1, 1, 5, 1, 2, 4, 0, 4, 0, 4, 5, 2, 1, 0, 2, 1, 0, 2, 4,
       2, 2, 2, 2, 2, 1, 3, 2, 5, 3, 3, 0, 0],
      0, [0, 0, 0, 0, 0, 0, 2, 5, 4, 4, 3]⟩),
    (false, ⟨[5, 2, 2, 4, 2, 3, 0, 0, 0, 0, 0], 0,
      [0, 0, 3, 0, 3, 2, 5, 4, 4, 4, 4, 3, 4, 1, 1, 3, 0, 3, 3, 1, 4, 2, 2, 3, 4, 4, 5, 1, 4, 5,
       5, 3, 2, 1, 5, 3, 2, 1, 5, 0, 0, 2, 0, 0, 3, 1, 0, 5, 1, 3, 1, 3, 1, 3, 1, 5, 0, 0, 4, 0,
       5, 2, 0, 5, 5, 2, 2, 2, 5, 1, 1, 3, 5, 5, 5, 1, 4, 4, 4, 4, 3, 1, 3, 1, 3, 4, 0, 3, 2, 0,
       3, 3, 4, 4, 4, 4, 5, 3, 4, 0, 2, 5, 5],
      5, [5, 5, 5, 5, 5, 2, 3, 5, 2, 1, 4]⟩),
    (true, regroupTarget63 xForm0) ]

/-- Exact single-pass symbolic certificate for Family 1: confirms all 12 intermediate forms are
valid, follow overflow pattern `010101010101`, and land on `regroupTarget63 xForm0`. -/
theorem xForm0_symbolic_cert :
    checkSymbolicPattern overflowPattern12 xForm0 (regroupTarget63 xForm0) = true :=
  checkSymbolicPattern_of_chain xChain xForm0 (regroupTarget63 xForm0) (by decide)

/-- Symbolic 12-step cycle and non-palindromicity for Family 1, all `m ≥ 6`. -/
theorem xFam_symbolic {m : ℕ} (hm : 6 ≤ m) :
    revAdd6^[12] (xFam m) = xFam (m + 3) ∧
    ∀ t < 12, ¬ IsPalindrome6 (revAdd6^[t] (xFam m)) := by
  have hcert := checkSymbolicPattern_sound overflowPattern12 xForm0 (regroupTarget63 xForm0) m
    xForm0_symbolic_cert (by simpa [overflowPattern12] using hm)
    (fun t ht => le_trans (overflowPattern12_prefix_count t ht) hm)
  refine ⟨?_, hcert.2⟩
  unfold xFam
  have h1 : revAdd6^[12] (formVal xForm0 m) = formVal (regroupTarget63 xForm0) (m - 6) := hcert.1
  rw [h1, formVal_regroup xForm0 (regroupTarget63 xForm0) 6 3 (m - 6) rfl rfl rfl rfl rfl]
  exact congrArg (formVal xForm0) (by omega)

private theorem xFam_direct_0 :
    revAdd6^[12] (xFam 0) = xFam 3 ∧ ∀ t < 12, ¬ IsPalindrome6 (revAdd6^[t] (xFam 0)) :=
  directCycle_sound (xForm0_valid.validMSB6 0) (by decide)

private theorem xFam_direct_1 :
    revAdd6^[12] (xFam 1) = xFam 4 ∧ ∀ t < 12, ¬ IsPalindrome6 (revAdd6^[t] (xFam 1)) :=
  directCycle_sound (xForm0_valid.validMSB6 1) (by decide)

private theorem xFam_direct_2 :
    revAdd6^[12] (xFam 2) = xFam 5 ∧ ∀ t < 12, ¬ IsPalindrome6 (revAdd6^[t] (xFam 2)) :=
  directCycle_sound (xForm0_valid.validMSB6 2) (by decide)

private theorem xFam_direct_3 :
    revAdd6^[12] (xFam 3) = xFam 6 ∧ ∀ t < 12, ¬ IsPalindrome6 (revAdd6^[t] (xFam 3)) :=
  directCycle_sound (xForm0_valid.validMSB6 3) (by decide)

private theorem xFam_direct_4 :
    revAdd6^[12] (xFam 4) = xFam 7 ∧ ∀ t < 12, ¬ IsPalindrome6 (revAdd6^[t] (xFam 4)) :=
  directCycle_sound (xForm0_valid.validMSB6 4) (by decide)

private theorem xFam_direct_5 :
    revAdd6^[12] (xFam 5) = xFam 8 ∧ ∀ t < 12, ¬ IsPalindrome6 (revAdd6^[t] (xFam 5)) :=
  directCycle_sound (xForm0_valid.validMSB6 5) (by decide)

/-- Combined 12-step cycle and non-palindrome theorem for Family 1, ALL `m ≥ 0`. -/
theorem xFam_cycle_and_no_pal (m : ℕ) :
    revAdd6^[12] (xFam m) = xFam (m + 3) ∧
    ∀ t < 12, ¬ IsPalindrome6 (revAdd6^[t] (xFam m)) := by
  match m with
  | 0 => exact xFam_direct_0
  | 1 => exact xFam_direct_1
  | 2 => exact xFam_direct_2
  | 3 => exact xFam_direct_3
  | 4 => exact xFam_direct_4
  | 5 => exact xFam_direct_5
  | m + 6 => exact xFam_symbolic (by omega)

/-- **Family 1 self-similar 12-step cycle**: `T^12(x(m)) = x(m + 3)` for every `m ≥ 0`. -/
theorem xFam_step12 : ∀ m : ℕ, revAdd6^[12] (xFam m) = xFam (m + 3) :=
  fun m => (xFam_cycle_and_no_pal m).1

/-- **Family 1 non-palindromicity**: none of `x(m), T(x(m)), ..., T^11(x(m))` is a base-6
palindrome, for every `m ≥ 0`. -/
theorem xFam_no_pal_lt12 : ∀ m : ℕ, ∀ t < 12, ¬ IsPalindrome6 (revAdd6^[t] (xFam m)) :=
  fun m => (xFam_cycle_and_no_pal m).2

/-- **Main Theorem (Family 1)**: every `x(m)` (`m ≥ 0`) is a base-6 Lychrel number. -/
theorem xFam_lychrel : ∀ m : ℕ, IsLychrel6 (xFam m) :=
  lychrel6_of_period_shift (by norm_num) xFam_step12 xFam_no_pal_lt12

/-- Corollary under the `j ≥ 1` Lychrel convention for Family 1. -/
theorem xFam_lychrel_pos : ∀ m : ℕ, ∀ j ≥ 1, ¬ IsPalindrome6 (revAdd6^[j] (xFam m)) :=
  fun m => (xFam_lychrel m).no_pal_pos

/-- Family 1 is strictly increasing (`m₁ < m₂ → x(m₁) < x(m₂)`), hence gives infinitely many
distinct base-6 Lychrel numbers. -/
theorem xFam_strictMono : StrictMono xFam := by
  intro m₁ m₂ hlt
  apply ofDigits6MSB_lt_of_length_lt (xForm0_valid.validMSB6 m₁) (xForm0_valid.validMSB6 m₂)
  rw [xFam_digits_length, xFam_digits_length]
  omega

/-- Exact base-10 value of the smallest Family 1 member `x(0)` (86 decimal digits). -/
theorem xFam_zero_eq :
    xFam 0 = 10597199767879923759424316990930862796672101123713351165673551415976972661719017382131 := by
  decide

/-! ### Family 2: `y(m)` (signal `101010101010`) -/

/-- Exact base-6 template of Family 2 (`tworun-1.md` §3.3). -/
def yForm0 : Form where
  A := [1, 3, 3, 4, 3]
  h := 0
  M := [0, 4, 3, 5, 0, 2, 2, 2, 2, 4, 4, 4, 1, 5, 4, 3, 5, 2, 4, 1, 5, 3, 2, 2, 2, 2, 1, 0, 0, 5,
        2, 2, 1, 0, 1, 1, 1, 0, 5, 1, 0, 4, 4, 4, 4, 1, 2, 5, 2, 5, 2, 5, 2, 1, 5, 3, 4, 5, 0, 1,
        4, 5, 1, 2, 0, 5, 1, 3, 1, 4, 0, 0, 2, 2, 1, 2, 2, 4, 0, 1, 4, 2, 4, 4, 4, 5, 2, 3, 3, 4,
        2, 2, 2, 2, 0, 5, 4, 4]
  l := 5
  Z := [5, 2, 4, 4, 3]

/-- Family 2 (`y(m)` for `m ≥ 0`), having `108 + 2m` base-6 digits. -/
def yFam (m : ℕ) : ℕ :=
  formVal yForm0 m

theorem yForm0_valid : ValidForm yForm0 :=
  validForm_of_bool (by decide)

theorem yFam_digits_length (m : ℕ) : (evalForm yForm0 m).length = 108 + 2 * m := by
  rw [evalForm_length]
  rfl

/-- Family 2's center `M₂` is the base-6 digit complement `d ↦ 5 - d` of Family 1's center `M₁`. -/
theorem yM_eq_complement_xM : yForm0.M = xForm0.M.map (5 - ·) := by
  decide

/-- Exact 12-row symbolic orbit of Family 2 (`tworun-1.md` §3.3), paired with its overflow bits
`010101010101`. -/
def yChain : List (Bool × Form) :=
  [ (false, ⟨[5, 2, 2, 1, 2], 5,
      [5, 3, 2, 5, 2, 4, 4, 5, 1, 2, 2, 1, 1, 4, 3, 2, 2, 0, 5, 2, 3, 5, 4, 3, 4, 4, 1, 0, 5, 0,
       5, 4, 0, 0, 3, 3, 0, 5, 0, 2, 0, 3, 2, 3, 5, 4, 2, 2, 2, 2, 2, 1, 4, 0, 4, 2, 2, 5, 2, 0,
       5, 0, 2, 3, 1, 0, 4, 0, 0, 4, 0, 1, 4, 4, 3, 5, 0, 3, 2, 0, 1, 2, 2, 3, 4, 1, 1, 2, 2, 0,
       4, 4, 4, 3, 0, 3, 2, 5],
      0, [3, 1, 2, 1, 4]⟩),
    (true, ⟨[1, 3, 3, 4, 3, 0], 0,
      [0, 5, 0, 0, 0, 0, 3, 3, 3, 1, 4, 4, 2, 3, 3, 0, 4, 4, 1, 5, 5, 1, 0, 4, 1, 3, 2, 2, 1, 3,
       1, 0, 2, 0, 2, 0, 5, 1, 4, 0, 4, 5, 5, 5, 2, 0, 2, 3, 4, 4, 4, 4, 4, 3, 0, 1, 4, 5, 5, 4,
       1, 4, 1, 0, 0, 1, 1, 2, 5, 1, 3, 0, 3, 3, 3, 1, 4, 0, 0, 4, 5, 1, 4, 5, 1, 2, 2, 2, 4, 4,
       2, 4, 3, 3, 0, 0, 0, 0, 4],
      5, [5, 5, 2, 4, 4, 3]⟩),
    (false, ⟨[5, 2, 2, 1, 2, 5], 5,
      [4, 5, 0, 0, 0, 4, 1, 2, 0, 0, 3, 0, 4, 5, 5, 0, 3, 0, 1, 3, 5, 1, 4, 5, 5, 0, 5, 2, 4, 5,
       0, 2, 3, 1, 2, 1, 0, 5, 5, 5, 4, 5, 4, 0, 2, 4, 1, 2, 3, 3, 3, 2, 0, 3, 3, 1, 4, 5, 3, 5,
       0, 0, 0, 0, 2, 1, 3, 3, 0, 4, 4, 3, 0, 0, 4, 5, 4, 2, 0, 4, 1, 0, 2, 5, 4, 5, 5, 1, 3, 0,
       0, 2, 0, 3, 0, 0, 0, 5, 5],
      0, [0, 3, 1, 2, 1, 4]⟩),
    (true, ⟨[1, 3, 3, 4, 3, 0, 0], 0,
      [0, 4, 4, 0, 0, 1, 1, 1, 4, 0, 1, 0, 2, 4, 5, 3, 5, 5, 0, 3, 1, 5, 4, 3, 5, 3, 1, 0, 0, 3,
       3, 1, 0, 0, 2, 4, 1, 1, 0, 0, 5, 2, 5, 2, 2, 0, 1, 1, 5, 1, 1, 0, 4, 2, 1, 5, 2, 3, 5, 2,
       4, 5, 5, 0, 1, 4, 3, 0, 5, 1, 4, 2, 5, 5, 1, 4, 5, 2, 4, 0, 1, 2, 1, 0, 0, 4, 5, 3, 2, 0,
       0, 0, 4, 2, 1, 0, 0, 1, 5, 3],
      5, [5, 5, 5, 2, 4, 4, 3]⟩),
    (false, ⟨[5, 2, 2, 1, 2, 5, 5], 5,
      [4, 3, 5, 0, 0, 2, 3, 5, 4, 0, 1, 3, 0, 4, 3, 4, 0, 0, 2, 4, 2, 4, 1, 3, 3, 5, 0, 5, 3, 1,
       5, 0, 0, 4, 0, 5, 2, 0, 5, 5, 2, 2, 2, 5, 1, 1, 3, 5, 5, 2, 2, 5, 5, 3, 2, 1, 5, 3, 2, 1,
       5, 0, 0, 2, 0, 0, 3, 1, 0, 5, 1, 3, 0, 0, 5, 4, 3, 1, 3, 1, 4, 3, 0, 5, 4, 4, 3, 5, 2, 1,
       0, 4, 5, 3, 2, 0, 1, 0, 3, 4],
      0, [0, 0, 3, 1, 2, 1, 4]⟩),
    (true, ⟨[1, 3, 3, 4, 3, 0, 0, 0], 0,
      [0, 3, 0, 5, 1, 0, 5, 1, 5, 2, 0, 3, 0, 0, 2, 2, 2, 5, 1, 0, 2, 4, 1, 3, 1, 2, 4, 1, 0, 0,
       3, 4, 0, 2, 1, 0, 5, 4, 1, 0, 4, 3, 5, 0, 4, 2, 4, 1, 5, 4, 4, 5, 5, 5, 0, 3, 3, 4, 5, 4,
       4, 4, 5, 0, 4, 5, 1, 1, 1, 1, 4, 3, 0, 5, 1, 5, 2, 0, 3, 1, 4, 2, 5, 1, 0, 3, 2, 1, 5, 5,
       2, 1, 3, 5, 0, 4, 0, 2, 0, 1, 2],
      5, [5, 5, 5, 5, 2, 4, 4, 3]⟩),
    (false, ⟨[5, 2, 2, 1, 2, 5, 5, 5], 5,
      [2, 4, 1, 1, 1, 5, 0, 1, 2, 3, 3, 2, 5, 1, 4, 5, 3, 1, 0, 3, 0, 5, 4, 3, 4, 2, 0, 0, 0, 4,
       1, 5, 1, 3, 3, 0, 3, 5, 0, 5, 3, 2, 4, 5, 1, 5, 5, 1, 5, 4, 3, 4, 5, 0, 5, 0, 1, 5, 5, 2,
       2, 5, 0, 5, 3, 5, 2, 3, 2, 0, 1, 3, 1, 1, 0, 1, 3, 3, 5, 0, 0, 3, 1, 0, 2, 5, 4, 2, 0, 2,
       2, 4, 3, 0, 5, 4, 2, 1, 0, 4, 3],
      0, [0, 0, 0, 3, 1, 2, 1, 4]⟩),
    (true, ⟨[1, 3, 3, 4, 3, 0, 0, 0, 0], 0,
      [0, 0, 2, 1, 2, 4, 3, 5, 2, 0, 1, 5, 4, 5, 4, 3, 4, 5, 1, 2, 0, 1, 0, 4, 1, 1, 3, 0, 1, 2,
       1, 2, 5, 4, 1, 0, 0, 1, 4, 1, 4, 5, 5, 4, 4, 3, 0, 4, 2, 5, 3, 1, 3, 4, 2, 4, 5, 3, 5, 3,
       5, 0, 4, 1, 5, 1, 0, 0, 0, 3, 5, 3, 1, 1, 1, 0, 4, 2, 1, 3, 5, 1, 0, 1, 2, 0, 5, 2, 3, 5,
       5, 0, 1, 5, 2, 0, 3, 3, 2, 2, 2, 5],
      5, [5, 5, 5, 5, 5, 2, 4, 4, 3]⟩),
    (false, ⟨[5, 2, 2, 1, 2, 5, 5, 5, 5], 5,
      [5, 2, 4, 4, 0, 1, 4, 2, 1, 1, 2, 5, 4, 3, 1, 2, 5, 1, 2, 2, 2, 0, 3, 5, 3, 5, 3, 1, 2, 3,
       5, 2, 2, 4, 1, 0, 2, 0, 5, 5, 5, 5, 3, 4, 2, 2, 5, 1, 1, 2, 4, 5, 3, 1, 0, 5, 3, 2, 4, 3,
       4, 5, 0, 0, 0, 1, 0, 1, 5, 3, 1, 4, 3, 2, 1, 3, 5, 3, 5, 4, 0, 1, 2, 3, 1, 5, 3, 1, 3, 4,
       4, 1, 2, 2, 1, 4, 1, 5, 3, 4, 3, 0],
      0, [0, 0, 0, 0, 3, 1, 2, 1, 4]⟩),
    (true, ⟨[1, 3, 3, 4, 3, 0, 0, 0, 0, 0], 0,
      [0, 0, 0, 3, 1, 5, 3, 2, 3, 3, 3, 4, 4, 3, 0, 3, 0, 4, 2, 5, 4, 3, 1, 2, 5, 1, 5, 0, 2, 5,
       1, 3, 4, 0, 3, 2, 0, 3, 1, 0, 0, 5, 4, 1, 2, 5, 0, 4, 1, 3, 0, 4, 3, 5, 2, 2, 4, 5, 5, 3,
       1, 4, 4, 5, 5, 0, 3, 0, 3, 3, 5, 4, 4, 0, 4, 3, 1, 5, 1, 5, 1, 0, 3, 4, 5, 3, 4, 5, 3, 1,
       3, 3, 3, 3, 3, 4, 2, 3, 0, 2, 2, 5, 5],
      5, [5, 5, 5, 5, 5, 5, 2, 4, 4, 3]⟩),
    (false, ⟨[5, 2, 2, 1, 2, 5, 5, 5, 5, 5], 5,
      [5, 5, 2, 5, 2, 3, 0, 1, 1, 1, 1, 2, 1, 4, 4, 2, 5, 2, 2, 4, 1, 3, 3, 2, 1, 1, 0, 4, 1, 0,
       0, 2, 3, 4, 0, 2, 3, 4, 0, 5, 5, 3, 5, 5, 2, 4, 5, 0, 4, 2, 4, 2, 4, 2, 4, 0, 5, 5, 1, 5,
       0, 3, 5, 0, 0, 3, 3, 3, 0, 4, 4, 2, 0, 0, 0, 4, 1, 1, 1, 1, 2, 4, 2, 4, 2, 1, 5, 2, 3, 5,
       2, 2, 1, 1, 1, 1, 0, 2, 1, 5, 3, 0, 0],
      0, [0, 0, 0, 0, 0, 3, 1, 2, 1, 4]⟩),
    (true, regroupTarget63 yForm0) ]

/-- Exact single-pass symbolic certificate for Family 2: confirms all 12 intermediate forms are
valid, follow overflow pattern `010101010101`, and land on `regroupTarget63 yForm0`. -/
theorem yForm0_symbolic_cert :
    checkSymbolicPattern overflowPattern12 yForm0 (regroupTarget63 yForm0) = true :=
  checkSymbolicPattern_of_chain yChain yForm0 (regroupTarget63 yForm0) (by decide)

/-- Symbolic 12-step cycle and non-palindromicity for Family 2, all `m ≥ 6`. -/
theorem yFam_symbolic {m : ℕ} (hm : 6 ≤ m) :
    revAdd6^[12] (yFam m) = yFam (m + 3) ∧
    ∀ t < 12, ¬ IsPalindrome6 (revAdd6^[t] (yFam m)) := by
  have hcert := checkSymbolicPattern_sound overflowPattern12 yForm0 (regroupTarget63 yForm0) m
    yForm0_symbolic_cert (by simpa [overflowPattern12] using hm)
    (fun t ht => le_trans (overflowPattern12_prefix_count t ht) hm)
  refine ⟨?_, hcert.2⟩
  unfold yFam
  have h1 : revAdd6^[12] (formVal yForm0 m) = formVal (regroupTarget63 yForm0) (m - 6) := hcert.1
  rw [h1, formVal_regroup yForm0 (regroupTarget63 yForm0) 6 3 (m - 6) rfl rfl rfl rfl rfl]
  exact congrArg (formVal yForm0) (by omega)

private theorem yFam_direct_0 :
    revAdd6^[12] (yFam 0) = yFam 3 ∧ ∀ t < 12, ¬ IsPalindrome6 (revAdd6^[t] (yFam 0)) :=
  directCycle_sound (yForm0_valid.validMSB6 0) (by decide)

private theorem yFam_direct_1 :
    revAdd6^[12] (yFam 1) = yFam 4 ∧ ∀ t < 12, ¬ IsPalindrome6 (revAdd6^[t] (yFam 1)) :=
  directCycle_sound (yForm0_valid.validMSB6 1) (by decide)

private theorem yFam_direct_2 :
    revAdd6^[12] (yFam 2) = yFam 5 ∧ ∀ t < 12, ¬ IsPalindrome6 (revAdd6^[t] (yFam 2)) :=
  directCycle_sound (yForm0_valid.validMSB6 2) (by decide)

private theorem yFam_direct_3 :
    revAdd6^[12] (yFam 3) = yFam 6 ∧ ∀ t < 12, ¬ IsPalindrome6 (revAdd6^[t] (yFam 3)) :=
  directCycle_sound (yForm0_valid.validMSB6 3) (by decide)

private theorem yFam_direct_4 :
    revAdd6^[12] (yFam 4) = yFam 7 ∧ ∀ t < 12, ¬ IsPalindrome6 (revAdd6^[t] (yFam 4)) :=
  directCycle_sound (yForm0_valid.validMSB6 4) (by decide)

private theorem yFam_direct_5 :
    revAdd6^[12] (yFam 5) = yFam 8 ∧ ∀ t < 12, ¬ IsPalindrome6 (revAdd6^[t] (yFam 5)) :=
  directCycle_sound (yForm0_valid.validMSB6 5) (by decide)

/-- Combined 12-step cycle and non-palindrome theorem for Family 2, ALL `m ≥ 0`. -/
theorem yFam_cycle_and_no_pal (m : ℕ) :
    revAdd6^[12] (yFam m) = yFam (m + 3) ∧
    ∀ t < 12, ¬ IsPalindrome6 (revAdd6^[t] (yFam m)) := by
  match m with
  | 0 => exact yFam_direct_0
  | 1 => exact yFam_direct_1
  | 2 => exact yFam_direct_2
  | 3 => exact yFam_direct_3
  | 4 => exact yFam_direct_4
  | 5 => exact yFam_direct_5
  | m + 6 => exact yFam_symbolic (by omega)

/-- **Family 2 self-similar 12-step cycle**: `T^12(y(m)) = y(m + 3)` for every `m ≥ 0`. -/
theorem yFam_step12 : ∀ m : ℕ, revAdd6^[12] (yFam m) = yFam (m + 3) :=
  fun m => (yFam_cycle_and_no_pal m).1

/-- **Family 2 non-palindromicity**: none of `y(m), T(y(m)), ..., T^11(y(m))` is a base-6
palindrome, for every `m ≥ 0`. -/
theorem yFam_no_pal_lt12 : ∀ m : ℕ, ∀ t < 12, ¬ IsPalindrome6 (revAdd6^[t] (yFam m)) :=
  fun m => (yFam_cycle_and_no_pal m).2

/-- **Main Theorem (Family 2)**: every `y(m)` (`m ≥ 0`) is a base-6 Lychrel number. -/
theorem yFam_lychrel : ∀ m : ℕ, IsLychrel6 (yFam m) :=
  lychrel6_of_period_shift (by norm_num) yFam_step12 yFam_no_pal_lt12

/-- Corollary under the `j ≥ 1` Lychrel convention for Family 2. -/
theorem yFam_lychrel_pos : ∀ m : ℕ, ∀ j ≥ 1, ¬ IsPalindrome6 (revAdd6^[j] (yFam m)) :=
  fun m => (yFam_lychrel m).no_pal_pos

/-- Family 2 is strictly increasing (`m₁ < m₂ → y(m₁) < y(m₂)`), hence gives infinitely many
distinct base-6 Lychrel numbers. -/
theorem yFam_strictMono : StrictMono yFam := by
  intro m₁ m₂ hlt
  apply ofDigits6MSB_lt_of_length_lt (yForm0_valid.validMSB6 m₁) (yForm0_valid.validMSB6 m₂)
  rw [yFam_digits_length, yFam_digits_length]
  omega

/-- Exact base-10 value of the smallest Family 2 member `y(0)` (84 decimal digits). -/
theorem yFam_zero_eq :
    yFam 0 = 293400065643122906317218502532643307621072769521307830691373332756338351497087823275 := by
  decide

/-! ### Disjointness of the Two Infinite Families -/

/-- **Complete disjointness**: `x(m) ≠ y(n)` for ALL `m, n : ℕ`.
In base 6, `x(m)` begins with `133535...` while `y(n)` begins with `13343...`, so their
canonical base-6 expansions already differ at the 4th digit (`5 ≠ 4`). -/
theorem xFam_disjoint_yFam : ∀ m n : ℕ, xFam m ≠ yFam n := by
  intro m n heq
  have hlist : evalForm xForm0 m = evalForm yForm0 n :=
    ofDigits6MSB_inj (xForm0_valid.validMSB6 m) (yForm0_valid.validMSB6 n) heq
  have h3 := congrArg (fun l => l[3]?) hlist
  simp [evalForm, xForm0, yForm0] at h3

/-- Existence of infinitely many base-6 Lychrel numbers (witnessed by `xFam`, and disjointly by
`yFam`). -/
theorem infinite_lychrel6 : Set.Infinite {n : ℕ | IsLychrel6 n} :=
  Set.infinite_of_injective_forall_mem xFam_strictMono.injective xFam_lychrel

end LychrelBase6
