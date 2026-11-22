module

public import LychrelBase6.Defs

import Mathlib.Tactic

/-!
# Carry-Automaton Engine: Lemma C, Lemma S, and Non-Palindrome Invariant

Formalizes the symbolic two-run base-6 carry automaton of `tworun-1.md` §3.2:
- `Form`: a parameterized base-6 digit template `A ++ h^k ++ M ++ l^k ++ Z` (MSB-first)
  with `|A| = |Z|`, nonzero leading digit, all digits `< 6`, and `h + l = 5`.
- **Lemma C (`carry_pair_sum_five`)**: a column summing to `5` passes any carry `c ∈ {0, 1}`
  unchanged and outputs `5` (if `c = 0`) or `0` (if `c = 1`).
- **Lemma S (`stepForm_sound`)**: a single computable symbolic step `stepForm` advances
  `formVal F k` under `revAdd6` for ALL run lengths `k` simultaneously (`k ≥ 0` on
  non-overflow steps, `k ≥ 1` on overflow steps).
- **Non-palindrome lemma (`form_not_palindrome`)**: every valid `Form` with `k ≥ 1` is
  strictly non-palindromic because `h + l = 5` is odd, forcing `h ≠ l` at mirror indices
  `|A|` from the top and `|Z|` from the bottom.
- Multi-step symbolic engine (`stepFormN_sound`, `stepFormN_no_pal`), run regrouping
  (`evalForm_regroup`, `formVal_regroup`), direct finite-case verification (`directCycle_sound`),
  and the period-shift induction principle (`lychrel6_of_period_shift`).
-/

@[expose] public section

namespace LychrelBase6

/-- A parameterized base-6 two-run digit template representing
`A ++ replicate k h ++ M ++ replicate k l ++ Z` in MSB-first order. -/
structure Form where
  A : List ℕ
  h : ℕ
  M : List ℕ
  l : ℕ
  Z : List ℕ
  deriving DecidableEq, Repr

/-- Instantiate a `Form` at run length `k` as an MSB-first base-6 digit list. -/
def evalForm (F : Form) (k : ℕ) : List ℕ :=
  F.A ++ List.replicate k F.h ++ F.M ++ List.replicate k F.l ++ F.Z

/-- Natural-number value of a `Form` instantiated at run length `k`. -/
def formVal (F : Form) (k : ℕ) : ℕ :=
  ofDigits6MSB (evalForm F k)

/-- Validity predicate for a `Form`: matching outer block lengths, non-empty `A` with nonzero
leading digit, all digits `< 6`, and facing run digits summing to `5`. -/
def ValidForm (F : Form) : Prop :=
  F.A.length = F.Z.length ∧
  F.A ≠ [] ∧
  F.A.head? ≠ some 0 ∧
  (∀ d ∈ F.A, d < 6) ∧
  F.h < 6 ∧
  (∀ d ∈ F.M, d < 6) ∧
  F.l < 6 ∧
  (∀ d ∈ F.Z, d < 6) ∧
  F.h + F.l = 5

/-- Decidable boolean checker for `ValidForm`. -/
def validFormBool (F : Form) : Bool :=
  (F.A.length == F.Z.length) &&
  (!F.A.isEmpty) &&
  (F.A.head? != some 0) &&
  (F.A.all (· < 6)) &&
  (decide (F.h < 6)) &&
  (F.M.all (· < 6)) &&
  (decide (F.l < 6)) &&
  (F.Z.all (· < 6)) &&
  (F.h + F.l == 5)

/-- Soundness of `validFormBool`. -/
theorem validForm_of_bool {F : Form} (hb : validFormBool F = true) : ValidForm F := by
  unfold validFormBool at hb
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', List.isEmpty_eq_false_iff,
    bne_iff_ne, List.all_eq_true, decide_eq_true_eq] at hb
  rcases hb with ⟨⟨⟨⟨⟨⟨⟨⟨hAZ, hAne⟩, hAhead⟩, hA⟩, hh⟩, hM⟩, hl⟩, hZ⟩, hsum⟩
  exact ⟨hAZ, hAne, hAhead, hA, hh, hM, hl, hZ, hsum⟩

/-- Every valid `Form` instantiates to a valid MSB-first base-6 digit list for every `k : ℕ`. -/
theorem ValidForm.validMSB6 {F : Form} (hF : ValidForm F) (k : ℕ) :
    ValidMSB6 (evalForm F k) := by
  rcases hF with ⟨_, hAne, hAhead, hA, hh, hM, hl, hZ, _⟩
  unfold evalForm
  refine ⟨?_, ?_, ?_⟩
  · simp [hAne]
  · intro d hd
    simp only [List.mem_append, List.mem_replicate] at hd
    rcases hd with ((((hd | ⟨_, rfl⟩) | hd) | ⟨_, rfl⟩) | hd)
    · exact hA d hd
    · exact hh
    · exact hM d hd
    · exact hl
    · exact hZ d hd
  · cases hAeq : F.A with
    | nil => exact (hAne hAeq).elim
    | cons a tl =>
      rw [hAeq] at hAhead
      simpa using hAhead

/-- Exact digit count of `evalForm F k`. -/
theorem evalForm_length (F : Form) (k : ℕ) :
    (evalForm F k).length = F.A.length + F.M.length + F.Z.length + 2 * k := by
  unfold evalForm
  simp only [List.length_append, List.length_replicate]
  omega

/-- Reversal of `evalForm F k` reverses the outer and middle blocks and swaps the two runs. -/
theorem evalForm_reverse (F : Form) (k : ℕ) :
    (evalForm F k).reverse =
      F.Z.reverse ++ List.replicate k F.l ++ F.M.reverse ++ List.replicate k F.h ++ F.A.reverse := by
  unfold evalForm
  simp [List.reverse_append, List.reverse_replicate, List.append_assoc]

/-- **Lemma C (the carry fact)**: in base 6, a column whose two digits satisfy `h + l = 5`
passes any incoming carry `c ∈ {0, 1}` unchanged and writes `5` if `c = 0`, `0` if `c = 1`. -/
theorem carry_pair_sum_five {h l c : ℕ} (hsum : h + l = 5) (hc : c ≤ 1) :
    (h + l + c) % 6 = (if c = 0 then 5 else 0) ∧ (h + l + c) / 6 = c := by
  split_ifs <;> omega

/-- Lemma C lifted to `k` consecutive columns: adding `replicate k l` and `replicate k h`
with `h + l = 5` and incoming carry `c ≤ 1` outputs `k` copies of `if c = 0 then 5 else 0`
and preserves carry `c`. -/
theorem addLSB6Aux_replicate :
    ∀ (k : ℕ) {h l c : ℕ}, h + l = 5 → c ≤ 1 →
      addLSB6Aux (List.replicate k l) (List.replicate k h) c =
        (List.replicate k (if c = 0 then 5 else 0), c)
  | 0, _, _, _, _, _ => rfl
  | k + 1, h, l, c, hsum, hc => by
    have hsum' : l + h = 5 := by omega
    have hC := carry_pair_sum_five hsum' hc
    simp only [List.replicate_succ, addLSB6Aux, hC.1, hC.2]
    rw [addLSB6Aux_replicate k hsum hc]

/-- Finalize one symbolic step according to the top carry `c3`. -/
def finishStepForm (A' M' Z' : List ℕ) (h' l' : ℕ) : ℕ → Form × Bool
  | 0 => (⟨A', h', M', l', Z'⟩, false)
  | _ + 1 => (⟨1 :: A', h', h' :: M', l', l' :: Z'⟩, true)

/-- Computable symbolic reverse-and-add step on a `Form`, returning `(F', overflow)`.
When `overflow = true` (`c3 = 1`), one digit from each run is absorbed into the outer and
middle blocks so that `|A'| = |Z'|` is preserved and the run length decreases by `1`. -/
def stepForm (F : Form) : Form × Bool :=
  match addLSB6Aux F.Z.reverse F.A 0 with
  | (zRev, c1) =>
    let l' := if c1 = 0 then 5 else 0
    match addLSB6Aux F.M.reverse F.M c1 with
    | (mRev, c2) =>
      let h' := if c2 = 0 then 5 else 0
      match addLSB6Aux F.A.reverse F.Z c2 with
      | (aRev, c3) => finishStepForm aRev.reverse mRev.reverse zRev.reverse h' l' c3

/-- Digit-list version of Lemma S: `revAddMSB6 (evalForm F k)` equals `evalForm` of the
symbolic successor form for every `k ≥ 0` (when `overflow = false`) or `k ≥ 1` (when
`overflow = true`). -/
theorem stepForm_eval {F : Form} (hF : ValidForm F) (k : ℕ)
    (hk : (stepForm F).2 = true → 1 ≤ k) :
    revAddMSB6 (evalForm F k) =
      evalForm (stepForm F).1 (if (stepForm F).2 then k - 1 else k) := by
  rcases hF with ⟨hAZ, _, _, hA, hh, hM, hl, hZ, hsum⟩
  set rZ := addLSB6Aux F.Z.reverse F.A 0
  set c1 := rZ.2
  set l' := if c1 = 0 then 5 else 0
  set rM := addLSB6Aux F.M.reverse F.M c1
  set c2 := rM.2
  set h' := if c2 = 0 then 5 else 0
  set rA := addLSB6Aux F.A.reverse F.Z c2
  set c3 := rA.2
  have hc1 : c1 ≤ 1 := addLSB6Aux_carry_le F.Z.reverse F.A 0
    (by simp [hAZ]) (fun d hd => hZ d (List.mem_reverse.mp hd)) hA (by omega)
  have hc2 : c2 ≤ 1 := addLSB6Aux_carry_le F.M.reverse F.M c1
    (by simp) (fun d hd => hM d (List.mem_reverse.mp hd)) hM hc1
  have hc3 : c3 ≤ 1 := addLSB6Aux_carry_le F.A.reverse F.Z c2
    (by simp [hAZ]) (fun d hd => hA d (List.mem_reverse.mp hd)) hZ hc2
  have hsum_comm : F.l + F.h = 5 := by omega
  have hadd :
      addLSB6Aux (evalForm F k).reverse (evalForm F k) 0 =
        (rZ.1 ++ List.replicate k l' ++ rM.1 ++ List.replicate k h' ++ rA.1, c3) := by
    rw [evalForm_reverse]
    unfold evalForm
    simp only [List.append_assoc]
    rw [addLSB6Aux_append F.Z.reverse F.A _ _ 0 (by simp [hAZ])]
    dsimp only
    change (rZ.1 ++ (addLSB6Aux (List.replicate k F.l ++ (F.M.reverse ++ (List.replicate k F.h ++ F.A.reverse)))
      (List.replicate k F.h ++ (F.M ++ (List.replicate k F.l ++ F.Z))) c1).1,
      (addLSB6Aux (List.replicate k F.l ++ (F.M.reverse ++ (List.replicate k F.h ++ F.A.reverse)))
      (List.replicate k F.h ++ (F.M ++ (List.replicate k F.l ++ F.Z))) c1).2) = _
    rw [addLSB6Aux_append (List.replicate k F.l) (List.replicate k F.h) _ _ c1 (by simp)]
    rw [addLSB6Aux_replicate k hsum hc1]
    dsimp only
    rw [addLSB6Aux_append F.M.reverse F.M _ _ c1 (by simp)]
    dsimp only
    change (rZ.1 ++ (List.replicate k l' ++ (rM.1 ++
      (addLSB6Aux (List.replicate k F.h ++ F.A.reverse) (List.replicate k F.l ++ F.Z) c2).1)),
      (addLSB6Aux (List.replicate k F.h ++ F.A.reverse) (List.replicate k F.l ++ F.Z) c2).2) = _
    rw [addLSB6Aux_append (List.replicate k F.h) (List.replicate k F.l) _ _ c2 (by simp)]
    rw [addLSB6Aux_replicate k hsum_comm hc2]
  have hrev_sum :
      (rZ.1 ++ List.replicate k l' ++ rM.1 ++ List.replicate k h' ++ rA.1).reverse =
        rA.1.reverse ++ List.replicate k h' ++ rM.1.reverse ++ List.replicate k l' ++ rZ.1.reverse := by
    simp [List.reverse_append, List.reverse_replicate, List.append_assoc]
  unfold revAddMSB6
  rw [hadd]
  have hstep_eq : stepForm F = finishStepForm rA.1.reverse rM.1.reverse rZ.1.reverse h' l' c3 := by
    unfold stepForm
    rfl
  rw [hstep_eq]
  cases hc3eq : c3 with
  | zero =>
    simp only [finishMSB6, finishStepForm, Bool.false_eq_true, ↓reduceIte]
    rw [hrev_sum]
    rfl
  | succ c3' =>
    have hc31 : c3' = 0 := by omega
    subst hc31
    have hstep_ov : (stepForm F).2 = true := by
      rw [hstep_eq, hc3eq]
      rfl
    have hk1 : 1 ≤ k := hk hstep_ov
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [finishMSB6, finishStepForm, ↓reduceIte, Nat.add_sub_cancel, evalForm]
    rw [hrev_sum]
    have hrep_h : List.replicate (k' + 1) h' = List.replicate k' h' ++ [h'] :=
      List.replicate_succ'
    have hrep_l : List.replicate (k' + 1) l' = List.replicate k' l' ++ [l'] :=
      List.replicate_succ'
    rw [hrep_h, hrep_l]
    simp [List.append_assoc]

/-- **Lemma S (symbolic step soundness)**: for any valid `Form`, `revAdd6 (formVal F k)`
equals `formVal` of the symbolic successor form for every `k ≥ 0` (when no overflow) or
`k ≥ 1` (when overflow). -/
theorem stepForm_sound {F : Form} (hF : ValidForm F) (k : ℕ)
    (hk : (stepForm F).2 = true → 1 ≤ k) :
    revAdd6 (formVal F k) =
      formVal (stepForm F).1 (if (stepForm F).2 then k - 1 else k) := by
  unfold formVal
  rw [← ofDigits6MSB_revAddMSB6 (hF.validMSB6 k), stepForm_eval hF k hk]

/-- **Non-palindrome lemma**: for ANY valid `Form` (which has `|A| = |Z|` and `h + l = 5`)
and ANY `k ≥ 1`, `formVal F k` is not a base-6 palindrome because the mirror positions at
index `|A|` from the top and `|Z|` from the bottom hold `h` and `l`, and `h + l = 5` is odd. -/
theorem form_not_palindrome {F : Form} (hF : ValidForm F) {k : ℕ} (hk : 1 ≤ k) :
    ¬ IsPalindrome6 (formVal F k) := by
  intro hpal
  rw [formVal, isPalindrome6_ofDigits6MSB (hF.validMSB6 k)] at hpal
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h1 : (evalForm F (k' + 1))[F.A.length]? = some F.h := by
    unfold evalForm
    simp only [List.append_assoc, List.replicate_succ]
    rw [List.getElem?_append_right (le_refl _)]
    simp
  have h2 : ((evalForm F (k' + 1)).reverse)[F.A.length]? = some F.l := by
    rw [evalForm_reverse]
    simp only [List.append_assoc, List.replicate_succ]
    have hlen : F.Z.reverse.length = F.A.length := by simp [hF.1]
    rw [← hlen, List.getElem?_append_right (le_refl _)]
    simp
  rw [hpal] at h2
  have hhl : F.h = F.l := Option.some.inj (h1.symm.trans h2)
  have hsum : F.h + F.l = 5 := hF.2.2.2.2.2.2.2.2
  omega

/-- Iterate `stepForm` `n` times, tracking `(currentForm, totalOverflowCount)`. -/
def stepFormN (F : Form) : ℕ → Form × ℕ
  | 0 => (F, 0)
  | n + 1 =>
    let prev := stepFormN F n
    let nxt := stepForm prev.1
    (nxt.1, prev.2 + if nxt.2 then 1 else 0)

/-- Boolean check that every intermediate symbolic form at steps `0, 1, ..., n - 1` is valid. -/
def allValidBefore (F : Form) : ℕ → Bool
  | 0 => true
  | n + 1 => allValidBefore F n && validFormBool (stepFormN F n).1

/-- Monotonicity of `allValidBefore`: validity before `n` implies validity before any `t ≤ n`. -/
theorem allValidBefore_of_le {F : Form} {t n : ℕ} (ht : t ≤ n)
    (h : allValidBefore F n = true) : allValidBefore F t = true := by
  induction n with
  | zero =>
    have : t = 0 := by omega
    subst this
    exact h
  | succ n ih =>
    by_cases htn : t = n + 1
    · subst htn; exact h
    · have hle : t ≤ n := by omega
      simp only [allValidBefore, Bool.and_eq_true] at h
      exact ih hle h.1

/-- Validity of step `t` extracted from `allValidBefore F n = true` for any `t < n`. -/
theorem validForm_stepFormN_of_lt {F : Form} {t n : ℕ} (ht : t < n)
    (h : allValidBefore F n = true) : ValidForm (stepFormN F t).1 := by
  have hle : allValidBefore F (t + 1) = true := allValidBefore_of_le ht h
  simp only [allValidBefore, Bool.and_eq_true] at hle
  exact validForm_of_bool hle.2

/-- Monotonicity of the cumulative overflow count `(stepFormN F t).2`. -/
theorem stepFormN_ov_mono {F : Form} {t n : ℕ} (h : t ≤ n) :
    (stepFormN F t).2 ≤ (stepFormN F n).2 := by
  induction n with
  | zero =>
    have : t = 0 := by omega
    subst this
    exact le_refl _
  | succ n ih =>
    by_cases htn : t = n + 1
    · subst htn; exact le_refl _
    · have hle : t ≤ n := by omega
      have h1 := ih hle
      simp only [stepFormN]
      omega

/-- Multi-step symbolic soundness: if every form before step `n` is valid and the cumulative
overflow count at step `n` is at most `m`, then `revAdd6^[n] (formVal F m)` equals
`formVal (stepFormN F n).1 (m - (stepFormN F n).2)`. -/
theorem stepFormN_sound {F : Form} (n m : ℕ)
    (hvalid : allValidBefore F n = true)
    (hm : (stepFormN F n).2 ≤ m) :
    revAdd6^[n] (formVal F m) = formVal (stepFormN F n).1 (m - (stepFormN F n).2) := by
  induction n with
  | zero => simp [stepFormN]
  | succ n ih =>
    simp only [allValidBefore, Bool.and_eq_true] at hvalid
    have hFn : ValidForm (stepFormN F n).1 := validForm_of_bool hvalid.2
    have hmn : (stepFormN F n).2 ≤ m := le_trans (stepFormN_ov_mono (Nat.le_succ n)) hm
    have hstep_ih := ih hvalid.1 hmn
    rw [Function.iterate_succ_apply', hstep_ih]
    have hstep := stepForm_sound hFn (m - (stepFormN F n).2) (by
      intro hov
      simp only [stepFormN, hov, ↓reduceIte] at hm
      omega)
    rw [hstep]
    simp only [stepFormN]
    cases h : (stepForm (stepFormN F n).1).2 <;> simp [Nat.sub_sub]

/-- Multi-step symbolic non-palindrome theorem: if every form before step `n` is valid and
every step `t < n` has `(stepFormN F t).2 + 1 ≤ m`, then no iterate `revAdd6^[t] (formVal F m)`
for `t < n` is a base-6 palindrome. -/
theorem stepFormN_no_pal {F : Form} (n m : ℕ)
    (hvalid : allValidBefore F n = true)
    (hm : ∀ t < n, (stepFormN F t).2 + 1 ≤ m) :
    ∀ t < n, ¬ IsPalindrome6 (revAdd6^[t] (formVal F m)) := by
  intro t ht
  have hvt : allValidBefore F t = true := allValidBefore_of_le (Nat.le_of_lt ht) hvalid
  have hFt : ValidForm (stepFormN F t).1 := validForm_stepFormN_of_lt ht hvalid
  have hmt : (stepFormN F t).2 + 1 ≤ m := hm t ht
  rw [stepFormN_sound t m hvt (by omega)]
  exact form_not_palindrome hFt (by omega)

/-- Exact run-regrouping lemma on digit lists: absorbing `p` run digits into the outer blocks
and `q` run digits into the middle block shifts the run length by `p + q`. -/
theorem evalForm_regroup (F F' : Form) (p q k : ℕ)
    (hA : F'.A = F.A ++ List.replicate p F.h)
    (hh : F'.h = F.h)
    (hM : F'.M = List.replicate q F.h ++ F.M ++ List.replicate q F.l)
    (hl : F'.l = F.l)
    (hZ : F'.Z = List.replicate p F.l ++ F.Z) :
    evalForm F' k = evalForm F (p + k + q) := by
  unfold evalForm
  rw [hA, hh, hM, hl, hZ]
  simp only [List.append_assoc]
  have h1 : List.replicate p F.h ++ (List.replicate k F.h ++ List.replicate q F.h) =
      List.replicate (p + k + q) F.h := by
    rw [← List.replicate_add, ← List.replicate_add, Nat.add_assoc]
  have h2 : List.replicate q F.l ++ (List.replicate k F.l ++ List.replicate p F.l) =
      List.replicate (p + k + q) F.l := by
    rw [← List.replicate_add, ← List.replicate_add]
    congr 1
    omega
  calc
    F.A ++ (List.replicate p F.h ++ (List.replicate k F.h ++ (List.replicate q F.h ++
        (F.M ++ (List.replicate q F.l ++ (List.replicate k F.l ++ (List.replicate p F.l ++ F.Z)))))))
      = F.A ++ ((List.replicate p F.h ++ (List.replicate k F.h ++ List.replicate q F.h)) ++
        (F.M ++ ((List.replicate q F.l ++ (List.replicate k F.l ++ List.replicate p F.l)) ++ F.Z))) := by
          simp only [List.append_assoc]
    _ = F.A ++ (List.replicate (p + k + q) F.h ++ (F.M ++ (List.replicate (p + k + q) F.l ++ F.Z))) := by
          rw [h1, h2]

/-- Run-regrouping lemma lifted to natural-number values `formVal`. -/
theorem formVal_regroup (F F' : Form) (p q k : ℕ)
    (hA : F'.A = F.A ++ List.replicate p F.h)
    (hh : F'.h = F.h)
    (hM : F'.M = List.replicate q F.h ++ F.M ++ List.replicate q F.l)
    (hl : F'.l = F.l)
    (hZ : F'.Z = List.replicate p F.l ++ F.Z) :
    formVal F' k = formVal F (p + k + q) := by
  unfold formVal
  rw [evalForm_regroup F F' p q k hA hh hM hl hZ]

/-- Single-pass linear symbolic cycle checker: verifies that starting from `F`, applying
`stepForm` along the exact overflow pattern `pat` visits only valid forms (`validFormBool`)
and lands on `Ftarget`. -/
def checkSymbolicPattern : List Bool → Form → Form → Bool
  | [], F, Ftarget => F == Ftarget
  | b :: bs, F, Ftarget =>
    validFormBool F &&
    match stepForm F with
    | (F', ov) => (ov == b) && checkSymbolicPattern bs F' Ftarget

/-- Soundness of `checkSymbolicPattern`: bridges a single linear pass of `stepForm` directly
to `revAdd6^[pat.length]` and non-palindromicity for every `m` large enough for the overflows. -/
theorem checkSymbolicPattern_sound :
    ∀ (pat : List Bool) (F Ftarget : Form) (m : ℕ),
      checkSymbolicPattern pat F Ftarget = true →
      pat.count true ≤ m →
      (∀ t < pat.length, (pat.take t).count true + 1 ≤ m) →
      revAdd6^[pat.length] (formVal F m) = formVal Ftarget (m - pat.count true) ∧
      ∀ t < pat.length, ¬ IsPalindrome6 (revAdd6^[t] (formVal F m))
  | [], F, Ftarget, m, hchk, _, _ => by
    simp only [checkSymbolicPattern, beq_iff_eq] at hchk
    exact ⟨by simp [hchk], fun t ht => by simp at ht⟩
  | b :: bs, F, Ftarget, m, hchk, hov, hpal => by
    unfold checkSymbolicPattern at hchk
    rcases hst : stepForm F with ⟨F', ov⟩
    rw [hst] at hchk
    simp only [Bool.and_eq_true, beq_iff_eq] at hchk
    rcases hchk with ⟨hval, hb, hrest⟩
    have hF : ValidForm F := validForm_of_bool hval
    have hm1 : 1 ≤ m := by
      have h0 := hpal 0 (by simp)
      simp at h0
      exact h0
    have hstep := stepForm_sound hF m (fun _ => hm1)
    rw [hst, hb] at hstep
    set m' := if b then m - 1 else m
    have hov' : bs.count true ≤ m' := by
      cases b <;> simp only [List.count_cons, beq_self_eq_true, ↓reduceIte] at hov <;>
        simp only [m', ↓reduceIte, Bool.false_eq_true] <;> omega
    have hpal' : ∀ t < bs.length, (bs.take t).count true + 1 ≤ m' := by
      intro t ht
      have h0 := hpal (t + 1) (by simpa using Nat.succ_lt_succ ht)
      cases b <;> simp only [List.take_succ_cons, List.count_cons, beq_self_eq_true,
        ↓reduceIte] at h0 <;> simp only [m', ↓reduceIte, Bool.false_eq_true] <;> omega
    have ih := checkSymbolicPattern_sound bs F' Ftarget m' hrest hov' hpal'
    refine ⟨?_, ?_⟩
    · rw [List.length_cons, Function.iterate_succ_apply, hstep, ih.1]
      congr 1
      cases b
      · simp [m']
      · simp [m', Nat.sub_sub]
        omega
    · intro t ht
      cases t with
      | zero =>
        simpa using form_not_palindrome hF hm1
      | succ t' =>
        rw [Function.iterate_succ_apply, hstep]
        exact ih.2 t' (by simpa using ht)

/-- Witnessed symbolic chain checker: verifies each single step `stepForm F == (Fnext, b)`
from ground literal to ground literal, keeping kernel reduction linear in the number of steps. -/
def checkSymbolicChain : List (Bool × Form) → Form → Form → Bool
  | [], F, Ftarget => F == Ftarget
  | (b, Fnext) :: rest, F, Ftarget =>
    validFormBool F && (stepForm F == (Fnext, b)) && checkSymbolicChain rest Fnext Ftarget

/-- Every passing witnessed chain certifies `checkSymbolicPattern` for its overflow pattern. -/
theorem checkSymbolicPattern_of_chain :
    ∀ (chain : List (Bool × Form)) (F Ftarget : Form),
      checkSymbolicChain chain F Ftarget = true →
      checkSymbolicPattern (chain.map Prod.fst) F Ftarget = true
  | [], F, Ftarget, h => h
  | (b, Fnext) :: rest, F, Ftarget, h => by
    simp only [checkSymbolicChain, Bool.and_eq_true, beq_iff_eq] at h
    rcases h with ⟨⟨hval, hst⟩, hrest⟩
    simp only [List.map_cons, checkSymbolicPattern, hst, hval, beq_self_eq_true, Bool.true_and]
    exact checkSymbolicPattern_of_chain rest Fnext Ftarget hrest

/-- Linear-pass finite-case checker: verifies in `n` calls to `revAddMSB6` that starting from
`ds`, none of the first `n` rows is palindromic and step `n` equals `dsTarget`. -/
def checkDirectCycleAux : ℕ → List ℕ → List ℕ → Bool
  | 0, ds, dsTarget => ds == dsTarget
  | n + 1, ds, dsTarget =>
    (ds.reverse != ds) && checkDirectCycleAux n (revAddMSB6 ds) dsTarget

/-- Soundness of `checkDirectCycleAux`: bridges the linear-pass digit-list check directly to
`revAdd6` and `IsPalindrome6` on `ℕ`. -/
theorem checkDirectCycleAux_sound :
    ∀ (n : ℕ) (ds dsTarget : List ℕ),
      ValidMSB6 ds →
      checkDirectCycleAux n ds dsTarget = true →
      revAdd6^[n] (ofDigits6MSB ds) = ofDigits6MSB dsTarget ∧
      ∀ t < n, ¬ IsPalindrome6 (revAdd6^[t] (ofDigits6MSB ds))
  | 0, ds, dsTarget, _, h => by
    simp only [checkDirectCycleAux, beq_iff_eq] at h
    exact ⟨by simp [h], fun t ht => by omega⟩
  | n + 1, ds, dsTarget, hds, h => by
    simp only [checkDirectCycleAux, Bool.and_eq_true, bne_iff_ne] at h
    have ih := checkDirectCycleAux_sound n (revAddMSB6 ds) dsTarget (revAddMSB6_valid hds) h.2
    refine ⟨?_, ?_⟩
    · rw [Function.iterate_succ_apply, ← ofDigits6MSB_revAddMSB6 hds]
      exact ih.1
    · intro t ht
      cases t with
      | zero =>
        simpa [isPalindrome6_ofDigits6MSB hds] using h.1
      | succ t' =>
        rw [Function.iterate_succ_apply, ← ofDigits6MSB_revAddMSB6 hds]
        exact ih.2 t' (by omega)

/-- Decidable finite-case checker for a 12-step cycle and non-palindromicity on concrete
MSB-first base-6 digit lists (used for small `m ∈ {0, 1, 2, 3, 4, 5}`). -/
def checkDirectCycle (ds dsTarget : List ℕ) : Bool :=
  checkDirectCycleAux 12 ds dsTarget

/-- Soundness of `checkDirectCycle`: bridges the pure digit-list check directly to `revAdd6`
and `IsPalindrome6` on `ℕ`. -/
theorem directCycle_sound {ds dsTarget : List ℕ} (hds : ValidMSB6 ds)
    (hchk : checkDirectCycle ds dsTarget = true) :
    revAdd6^[12] (ofDigits6MSB ds) = ofDigits6MSB dsTarget ∧
    ∀ t < 12, ¬ IsPalindrome6 (revAdd6^[t] (ofDigits6MSB ds)) :=
  checkDirectCycleAux_sound 12 ds dsTarget hds hchk

/-- Period-shift induction principle: if `revAdd6^[P] (f m) = f (m + δ)` for all `m` and no
intermediate step `t < P` is a base-6 palindrome for any `m`, then every `f m` is a base-6
Lychrel number. -/
theorem lychrel6_of_period_shift {f : ℕ → ℕ} {P δ : ℕ} (hP : 0 < P)
    (hstep : ∀ m : ℕ, revAdd6^[P] (f m) = f (m + δ))
    (hnopal : ∀ m : ℕ, ∀ t < P, ¬ IsPalindrome6 (revAdd6^[t] (f m))) :
    ∀ m : ℕ, IsLychrel6 (f m) := by
  have hmul : ∀ q m : ℕ, revAdd6^[P * q] (f m) = f (m + δ * q) := by
    intro q
    induction q with
    | zero => intro m; simp
    | succ q ih =>
      intro m
      rw [Nat.mul_succ, Function.iterate_add_apply, hstep m, ih (m + δ)]
      ring_nf
  intro m j
  have hj : j = j % P + P * (j / P) := by
    have := Nat.div_add_mod j P
    omega
  rw [hj, Function.iterate_add_apply, hmul (j / P) m]
  exact hnopal (m + δ * (j / P)) (j % P) (Nat.mod_lt j hP)

end LychrelBase6
