module

public import LychrelBase6.Families
public import Mathlib.Data.Set.Card

import Mathlib.Tactic

/-!
# Complement Duality, Six-Seed Orbit Structure, and Counting Bounds (`LychrelBase6`)

Upgrades the formal theory of `LychrelBase6` across four pillars:

1. **Base-6 Digit-Complement Duality (`compDigit6`, `compList6`)**:
   - Proves the column-level base-6 complement law
     `(5 - a) + (5 - b) + (1 - c) = 11 - (a + b + c)`, flipping carries `c ↦ 1 - c`,
     complementing output digits `d ↦ 5 - d`, and swapping complementary runs `(5^m, 0^m) ↔ (0^m, 5^m)`.
   - Lifts complement duality to arbitrary equal-length column additions (`addLSB6Aux_compList6`),
     center self-additions (`center_block_complement_duality`), and symbolic `Form` transitions
     (`stepForm_center_duality`), and verifies across all 12 rows of `xChain` and `yChain` that
     every interior block satisfies `M₂^{(t)} = compList6 M₁^{(t)}` with opposite carry signals
     `010101010101` and `101010101010`.

2. **General Base-`B` Center-Automaton Complement Isomorphism `φ` (`tworun-1.md` §1)**:
   - Formalizes the two-run center automaton over any base `B ≥ 2` (`PhaseState`, `CenterNode`,
     `startCenterNode`, `fullColumn`, `advanceAux`, `centerEdge`, `closes`) and proves that `φ`
     maps the start node of `(B, ov, cin)` to `(B, ov, 1 - cin)` (`startCenterNode_phi`),
     preserves transitions (`centerEdge_phi`, `centerPath_phi`), and preserves center closures of
     both parities (`closes_phi`).

3. **Exact Digit Lengths & Six-Seed Forward-Orbit Structure**:
   - Proves strict monotonicity of forward `revAdd6` trajectories for every `n ≥ 1`
     (`revAdd6_iterate_strictMono`), Lychrel forward-invariance (`IsLychrel6.iterate`), exact
     base-6 digit lengths `(Nat.digits 6 (revAdd6^[t] (xFam m))).length = 110 + 2 * m + t / 2`
     and `(Nat.digits 6 (revAdd6^[t] (yFam m))).length = 108 + 2 * m + t / 2` for all `m, t : ℕ`,
     six-root period generation, and complete pairwise disjointness of all six trajectories
     `{revAdd6^[t] (xFam r) | t}` and `{revAdd6^[t] (yFam r) | t}` (`r ∈ {0, 1, 2}`).

4. **Explicit Quantitative Counting Lower Bounds**:
   - Constructs an explicit finite witness `familyOrbitsFinset D` of base-6 Lychrel numbers
     strictly below `6 ^ D` of exact cardinality `12 * (D - 110)` for all `D ≥ 113`, proving
     `12 * (D - 110) ≤ Set.ncard {n : ℕ | n ≤ 6 ^ D ∧ IsLychrel6 n}` for all `D ≥ 113`,
     `max 10 (24 * N) ≤ Set.ncard {n : ℕ | n ≤ 6 ^ (110 + 2 * N) ∧ IsLychrel6 n}` for all `N : ℕ`,
     and `max 10 (72 * k) ≤ Set.ncard {n : ℕ | n ≤ 6 ^ (110 + 6 * k) ∧ IsLychrel6 n}` for all `k : ℕ`.
-/

@[expose] public section

namespace LychrelBase6

set_option maxRecDepth 4096

/-! ## Section 1: Base-6 Digit-Complement Duality (`d ↦ 5 - d`) -/

/-- Base-6 digit complement `φ(d) = 5 - d`. -/
def compDigit6 (d : ℕ) : ℕ :=
  5 - d

/-- Digit-by-digit base-6 complement of a digit list. -/
def compList6 (ds : List ℕ) : List ℕ :=
  ds.map compDigit6

/-- Every complemented base-6 digit is strictly less than `6`. -/
theorem compDigit6_lt_six (d : ℕ) : compDigit6 d < 6 := by
  unfold compDigit6
  omega

/-- `compDigit6` is an involution on valid base-6 digits (`d < 6`). -/
theorem compDigit6_involutive {d : ℕ} (hd : d < 6) :
    compDigit6 (compDigit6 d) = d := by
  unfold compDigit6
  omega

/-- `compList6` preserves list length. -/
theorem compList6_length (ds : List ℕ) : (compList6 ds).length = ds.length := by
  simp [compList6]

/-- Every entry of `compList6 ds` is `< 6`. -/
theorem compList6_digits_lt (ds : List ℕ) : ∀ d ∈ compList6 ds, d < 6 := by
  intro d hd
  simp only [compList6, List.mem_map] at hd
  rcases hd with ⟨x, _, rfl⟩
  exact compDigit6_lt_six x

/-- `compList6` is an involution on lists of base-6 digits (`d < 6`). -/
theorem compList6_involutive {ds : List ℕ} (hds : ∀ d ∈ ds, d < 6) :
    compList6 (compList6 ds) = ds := by
  induction ds with
  | nil => rfl
  | cons d tl ih =>
    have hd : d < 6 := hds d (List.mem_cons_self ..)
    have htl : ∀ x ∈ tl, x < 6 := fun x hx => hds x (List.mem_cons_of_mem d hx)
    simp only [compList6, List.map_cons]
    rw [compDigit6_involutive hd]
    exact congrArg (d :: ·) (ih htl)

/-- `compList6` distributes over list concatenation. -/
theorem compList6_append (ds₁ ds₂ : List ℕ) :
    compList6 (ds₁ ++ ds₂) = compList6 ds₁ ++ compList6 ds₂ := by
  simp [compList6]

/-- `compList6` commutes with list reversal. -/
theorem compList6_reverse (ds : List ℕ) :
    (compList6 ds).reverse = compList6 ds.reverse := by
  simp [compList6, List.map_reverse]

/-- `compList6` maps `replicate k d` to `replicate k (compDigit6 d)`. -/
theorem compList6_replicate (k d : ℕ) :
    compList6 (List.replicate k d) = List.replicate k (compDigit6 d) := by
  simp [compList6]

/-- `compList6` swaps the two complementary base-6 runs `5^m` and `0^m`. -/
theorem compList6_runs_swap (m : ℕ) :
    compList6 (List.replicate m 5) = List.replicate m 0 ∧
    compList6 (List.replicate m 0) = List.replicate m 5 := by
  simp [compList6, compDigit6]

/-- Flipping a carry bit `c ↦ 1 - c` (`c ≤ 1`) complements the Lemma C output digit
`if c = 0 then 5 else 0`. -/
theorem runDigit_of_comp_carry {c : ℕ} (hc : c ≤ 1) :
    (if 1 - c = 0 then 5 else 0) = compDigit6 (if c = 0 then 5 else 0) := by
  unfold compDigit6
  split_ifs <;> omega

/-- **Single-column base-6 complement identity**: for digits `a, b < 6` and carry `c ≤ 1`,
`(5 - a) + (5 - b) + (1 - c) = 11 - (a + b + c)`, complementing the output digit modulo `6`
and flipping the carry-out `c_out ↦ 1 - c_out`. -/
theorem column_complement_duality {a b c : ℕ} (ha : a < 6) (hb : b < 6) (hc : c ≤ 1) :
    compDigit6 a + compDigit6 b + (1 - c) = 11 - (a + b + c) ∧
    (compDigit6 a + compDigit6 b + (1 - c)) % 6 = compDigit6 ((a + b + c) % 6) ∧
    (compDigit6 a + compDigit6 b + (1 - c)) / 6 = 1 - (a + b + c) / 6 := by
  unfold compDigit6
  refine ⟨by omega, by omega, by omega⟩

/-- **Multi-column base-6 complement duality**: complementing two equal-length LSB-first base-6
digit lists and flipping the incoming carry `c ↦ 1 - c` complements every output digit and flips
the outgoing carry `c_out ↦ 1 - c_out`. -/
theorem addLSB6Aux_compList6 :
    ∀ (as bs : List ℕ) (c : ℕ),
      as.length = bs.length →
      (∀ d ∈ as, d < 6) →
      (∀ d ∈ bs, d < 6) →
      c ≤ 1 →
      addLSB6Aux (compList6 as) (compList6 bs) (1 - c) =
        (compList6 (addLSB6Aux as bs c).1, 1 - (addLSB6Aux as bs c).2)
  | [], [], c, _, _, _, _ => by simp [compList6, addLSB6Aux]
  | a :: as, b :: bs, c, hlen, has, hbs, hc => by
    have hlen' : as.length = bs.length := by simpa using hlen
    have ha : a < 6 := has a (List.mem_cons_self ..)
    have hb : b < 6 := hbs b (List.mem_cons_self ..)
    have hcol := column_complement_duality ha hb hc
    have hc' : (a + b + c) / 6 ≤ 1 := by omega
    have ih := addLSB6Aux_compList6 as bs ((a + b + c) / 6) hlen'
      (fun d hd => has d (List.mem_cons_of_mem a hd))
      (fun d hd => hbs d (List.mem_cons_of_mem b hd)) hc'
    simp only [compList6, List.map_cons, addLSB6Aux]
    change ((compDigit6 a + compDigit6 b + (1 - c)) % 6 ::
        (addLSB6Aux (compList6 as) (compList6 bs) ((compDigit6 a + compDigit6 b + (1 - c)) / 6)).1,
        (addLSB6Aux (compList6 as) (compList6 bs) ((compDigit6 a + compDigit6 b + (1 - c)) / 6)).2) = _
    rw [hcol.2.1, hcol.2.2, ih]
    rfl
  | [], _ :: _, _, hlen, _, _, _ => by simp at hlen
  | _ :: _, [], _, hlen, _, _, _ => by simp at hlen

/-- **Center-block complement duality**: adding `compList6 M` to its own reversal with incoming
carry `1 - c₁` produces the exact digit complement of `M^R + M` (with carry `c₁`) and flips the
outgoing center carry `c₂ ↦ 1 - c₂`. -/
theorem center_block_complement_duality {M : List ℕ} {c₁ : ℕ}
    (hM : ∀ d ∈ M, d < 6) (hc₁ : c₁ ≤ 1) :
    addLSB6Aux (compList6 M).reverse (compList6 M) (1 - c₁) =
      (compList6 (addLSB6Aux M.reverse M c₁).1, 1 - (addLSB6Aux M.reverse M c₁).2) := by
  rw [compList6_reverse]
  exact addLSB6Aux_compList6 M.reverse M c₁ (by simp)
    (fun d hd => hM d (List.mem_reverse.mp hd)) hM hc₁

/-- Carry `c₁` leaving the lower outer addition `Z^R + A` into the lower run in Lemma S. -/
def lowCarry (F : Form) : ℕ :=
  (addLSB6Aux F.Z.reverse F.A 0).2

/-- Carry `c₂` leaving the middle self-addition `M^R + M` into the upper run in Lemma S. -/
def highCarry (F : Form) : ℕ :=
  (addLSB6Aux F.M.reverse F.M (lowCarry F)).2

/-- Carry `c₃` (overflow bit) leaving the upper outer addition `A^R + Z` in Lemma S. -/
def topCarry (F : Form) : ℕ :=
  (addLSB6Aux F.A.reverse F.Z (highCarry F)).2

/-- For any valid `Form`, all three Lemma S carries `lowCarry`, `highCarry`, `topCarry` lie in `{0, 1}`. -/
theorem ValidForm.carries_le_one {F : Form} (hF : ValidForm F) :
    lowCarry F ≤ 1 ∧ highCarry F ≤ 1 ∧ topCarry F ≤ 1 := by
  rcases hF with ⟨hAZ, _, _, hA, _, hM, _, hZ, _⟩
  have hc1 : lowCarry F ≤ 1 := addLSB6Aux_carry_le F.Z.reverse F.A 0
    (by simp [hAZ]) (fun d hd => hZ d (List.mem_reverse.mp hd)) hA (by omega)
  have hc2 : highCarry F ≤ 1 := addLSB6Aux_carry_le F.M.reverse F.M (lowCarry F)
    (by simp) (fun d hd => hM d (List.mem_reverse.mp hd)) hM hc1
  have hc3 : topCarry F ≤ 1 := addLSB6Aux_carry_le F.A.reverse F.Z (highCarry F)
    (by simp [hAZ]) (fun d hd => hA d (List.mem_reverse.mp hd)) hZ hc2
  exact ⟨hc1, hc2, hc3⟩

/-- **Symbolic `stepForm` Center Duality Theorem**: if two forms `F₁, F₂` (`F₁` valid) have
complementary centers `F₂.M = compList6 F₁.M`, complementary incoming low-run carries
`lowCarry F₂ = 1 - lowCarry F₁`, and the same overflow bit `(stepForm F₂).2 = (stepForm F₁).2`,
then `F₂` has complementary outgoing center carry `highCarry F₂ = 1 - highCarry F₁`, its
successor center `(stepForm F₂).1.M` is the exact base-6 complement `compList6 (stepForm F₁).1.M`
(both with and without overflow), and its successor run digits are complemented/swapped. -/
theorem stepForm_center_duality {F₁ F₂ : Form} (hF₁ : ValidForm F₁)
    (hM : F₂.M = compList6 F₁.M)
    (hc₁ : lowCarry F₂ = 1 - lowCarry F₁)
    (hov : (stepForm F₂).2 = (stepForm F₁).2) :
    highCarry F₂ = 1 - highCarry F₁ ∧
    (stepForm F₂).1.M = compList6 (stepForm F₁).1.M ∧
    (stepForm F₂).1.h = compDigit6 (stepForm F₁).1.h ∧
    (stepForm F₂).1.l = compDigit6 (stepForm F₁).1.l := by
  have hc1_le : lowCarry F₁ ≤ 1 := hF₁.carries_le_one.1
  have hc2_le : highCarry F₁ ≤ 1 := hF₁.carries_le_one.2.1
  have hM₁_lt : ∀ d ∈ F₁.M, d < 6 := hF₁.2.2.2.2.2.1
  have hcenter := center_block_complement_duality hM₁_lt hc1_le
  have hc2_eq : highCarry F₂ = 1 - highCarry F₁ := by
    unfold highCarry
    rw [hM, hc₁, hcenter]
  have hmRev_eq :
      (addLSB6Aux F₂.M.reverse F₂.M (lowCarry F₂)).1.reverse =
        compList6 (addLSB6Aux F₁.M.reverse F₁.M (lowCarry F₁)).1.reverse := by
    rw [hM, hc₁, hcenter, compList6_reverse]
  have hl'_eq : (if lowCarry F₂ = 0 then 5 else 0) =
      compDigit6 (if lowCarry F₁ = 0 then 5 else 0) := by
    rw [hc₁]
    exact runDigit_of_comp_carry hc1_le
  have hh'_eq : (if highCarry F₂ = 0 then 5 else 0) =
      compDigit6 (if highCarry F₁ = 0 then 5 else 0) := by
    rw [hc2_eq]
    exact runDigit_of_comp_carry hc2_le
  have hst₁ : stepForm F₁ = finishStepForm
      (addLSB6Aux F₁.A.reverse F₁.Z (highCarry F₁)).1.reverse
      (addLSB6Aux F₁.M.reverse F₁.M (lowCarry F₁)).1.reverse
      (addLSB6Aux F₁.Z.reverse F₁.A 0).1.reverse
      (if highCarry F₁ = 0 then 5 else 0)
      (if lowCarry F₁ = 0 then 5 else 0)
      (topCarry F₁) := rfl
  have hst₂ : stepForm F₂ = finishStepForm
      (addLSB6Aux F₂.A.reverse F₂.Z (highCarry F₂)).1.reverse
      (addLSB6Aux F₂.M.reverse F₂.M (lowCarry F₂)).1.reverse
      (addLSB6Aux F₂.Z.reverse F₂.A 0).1.reverse
      (if highCarry F₂ = 0 then 5 else 0)
      (if lowCarry F₂ = 0 then 5 else 0)
      (topCarry F₂) := rfl
  rw [hst₁, hst₂] at hov ⊢
  refine ⟨hc2_eq, ?_⟩
  cases htop₁ : topCarry F₁ <;> cases htop₂ : topCarry F₂
  · simp [finishStepForm, hmRev_eq, hh'_eq, hl'_eq]
  · rw [htop₁, htop₂] at hov
    simp [finishStepForm] at hov
  · rw [htop₁, htop₂] at hov
    simp [finishStepForm] at hov
  · simp [finishStepForm, hmRev_eq, hh'_eq, hl'_eq, compList6]

/-- `yForm0`'s center is `compList6 xForm0.M`, with complemented/swapped run digits `(0, 5)`. -/
theorem yForm0_M_eq_compList6 :
    yForm0.M = compList6 xForm0.M ∧
    yForm0.h = compDigit6 xForm0.h ∧
    yForm0.l = compDigit6 xForm0.l := by
  decide

/-- Across all 12 rows `t = 0..11` of `xChain` and `yChain`, every interior block satisfies
`yChain[t].2.M = compList6 (xChain[t].2.M)`, run digits are complemented, and overflow flags match. -/
theorem xChain_yChain_center_duality :
    xChain.length = 12 ∧
    yChain.length = 12 ∧
    ∀ t : Fin 12,
      (yChain[t.val]).2.M = compList6 (xChain[t.val]).2.M ∧
      (yChain[t.val]).2.h = compDigit6 (xChain[t.val]).2.h ∧
      (yChain[t.val]).2.l = compDigit6 (xChain[t.val]).2.l ∧
      (yChain[t.val]).1 = (xChain[t.val]).1 := by
  decide

/-- Helper connecting `stepFormN` directly to the ground forms of a passing `checkSymbolicChain`. -/
theorem stepFormN_eq_of_chain (dflt : Form) :
    ∀ (chain : List (Bool × Form)) (F Ftarget : Form),
      checkSymbolicChain chain F Ftarget = true →
      ∀ t ≤ chain.length,
        (stepFormN F t).1 = (F :: chain.map Prod.snd).getD t dflt ∧
        (stepFormN F t).2 = ((chain.map Prod.fst).take t).count true
  | [], F, _, _, t, ht => by
    have ht0 : t = 0 := by simpa using ht
    subst ht0
    simp [stepFormN]
  | (b, Fnext) :: rest, F, Ftarget, hchk, t, ht => by
    simp only [checkSymbolicChain, Bool.and_eq_true, beq_iff_eq] at hchk
    rcases hchk with ⟨⟨_, hstep⟩, hrest⟩
    have ih := stepFormN_eq_of_chain dflt rest Fnext Ftarget hrest
    have hshift : ∀ k : ℕ, stepFormN F (k + 1) =
        ((stepFormN Fnext k).1, (stepFormN Fnext k).2 + if b then 1 else 0) := by
      intro k
      induction k with
      | zero => simp [stepFormN, hstep]
      | succ k ihk =>
        change (let prev := stepFormN F (k + 1)
          let nxt := stepForm prev.1
          (nxt.1, prev.2 + if nxt.2 then 1 else 0)) = _
        rw [ihk]
        simp only [stepFormN]
        exact Prod.ext rfl (by omega)
    cases t with
    | zero => simp [stepFormN]
    | succ t' =>
      have ht' : t' ≤ rest.length := by simpa using ht
      have iht := ih t' ht'
      rw [hshift t']
      refine ⟨?_, ?_⟩
      · simpa using iht.1
      · simp only [List.map_cons, List.take_succ_cons, List.count_cons]
        rw [iht.2]
        cases b <;> simp [Nat.add_comm]

/-- Witnessed chain certificate for `xChain`. -/
theorem xChain_check : checkSymbolicChain xChain xForm0 (regroupTarget63 xForm0) = true := by
  decide

/-- Witnessed chain certificate for `yChain`. -/
theorem yChain_check : checkSymbolicChain yChain yForm0 (regroupTarget63 yForm0) = true := by
  decide

/-- Ground list of the 13 symbolic forms `t = 0..12` of Family 1 (`x`). -/
def xForms13 : List Form :=
  xForm0 :: xChain.map Prod.snd

/-- Ground list of the 13 symbolic forms `t = 0..12` of Family 2 (`y`). -/
def yForms13 : List Form :=
  yForm0 :: yChain.map Prod.snd

/-- `stepFormN xForm0 t` equals `(xForms13.getD t xForm0, t / 2)` for every `t ≤ 12`. -/
theorem stepFormN_xForm0_eq {t : ℕ} (ht : t ≤ 12) :
    (stepFormN xForm0 t).1 = xForms13.getD t xForm0 ∧ (stepFormN xForm0 t).2 = t / 2 := by
  have h := stepFormN_eq_of_chain xForm0 xChain xForm0 (regroupTarget63 xForm0) xChain_check t ht
  refine ⟨h.1, ?_⟩
  rw [h.2]
  interval_cases t <;> decide

/-- `stepFormN yForm0 t` equals `(yForms13.getD t yForm0, t / 2)` for every `t ≤ 12`. -/
theorem stepFormN_yForm0_eq {t : ℕ} (ht : t ≤ 12) :
    (stepFormN yForm0 t).1 = yForms13.getD t yForm0 ∧ (stepFormN yForm0 t).2 = t / 2 := by
  have h := stepFormN_eq_of_chain yForm0 yChain yForm0 (regroupTarget63 yForm0) yChain_check t ht
  refine ⟨h.1, ?_⟩
  rw [h.2]
  interval_cases t <;> decide

/-- Across all 13 symbolic rows `t = 0..12`, `(stepFormN yForm0 t).1.M = compList6 (stepFormN xForm0 t).1.M`
with complemented run digits. -/
theorem stepFormN_xForm0_yForm0_duality {t : ℕ} (ht : t ≤ 12) :
    (stepFormN yForm0 t).1.M = compList6 (stepFormN xForm0 t).1.M ∧
    (stepFormN yForm0 t).1.h = compDigit6 (stepFormN xForm0 t).1.h ∧
    (stepFormN yForm0 t).1.l = compDigit6 (stepFormN xForm0 t).1.l := by
  rw [(stepFormN_xForm0_eq ht).1, (stepFormN_yForm0_eq ht).1]
  interval_cases t <;> decide

/-- Alternating carry signal `010101010101` of Family 1. -/
def carrySignal01 : List ℕ :=
  [0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1]

/-- Complementary alternating carry signal `101010101010` of Family 2. -/
def carrySignal10 : List ℕ :=
  [1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0]

/-- Across all 12 steps `t = 0..11`, `x` and `y` realize opposite interior carry signals
(`010101010101` vs `101010101010` for `c₁`, and `101010101010` vs `010101010101` for `c₂`)
and the identical top-carry overflow signal `010101010101` for `c₃`. -/
theorem xForms_yForms_carry_signals :
    (List.range 12).map (fun t => lowCarry (xForms13.getD t xForm0)) = carrySignal01 ∧
    (List.range 12).map (fun t => lowCarry (yForms13.getD t yForm0)) = carrySignal10 ∧
    (List.range 12).map (fun t => highCarry (xForms13.getD t xForm0)) = carrySignal10 ∧
    (List.range 12).map (fun t => highCarry (yForms13.getD t yForm0)) = carrySignal01 ∧
    (List.range 12).map (fun t => topCarry (xForms13.getD t xForm0)) = carrySignal01 ∧
    (List.range 12).map (fun t => topCarry (yForms13.getD t yForm0)) = carrySignal01 := by
  decide

/-- Stepwise complementary carries `c₁` and `c₂` and matching overflow `c₃` across `t < 12`. -/
theorem stepFormN_carries_duality {t : ℕ} (ht : t < 12) :
    lowCarry (stepFormN yForm0 t).1 = 1 - lowCarry (stepFormN xForm0 t).1 ∧
    highCarry (stepFormN yForm0 t).1 = 1 - highCarry (stepFormN xForm0 t).1 ∧
    topCarry (stepFormN yForm0 t).1 = topCarry (stepFormN xForm0 t).1 := by
  have hle : t ≤ 12 := Nat.le_of_lt ht
  rw [(stepFormN_xForm0_eq hle).1, (stepFormN_yForm0_eq hle).1]
  interval_cases t <;> decide

/-! ## Section 2: General Base-`B` Center-Automaton Complement Isomorphism `φ` -/

/-- **Step 0 (`tworun-1.md` §1)**: for any base `B ≥ 2` and sum `v < 2 * B`, setting
`v* = 2 * B - 1 - v` satisfies `v* / B = 1 - v / B` and `v* % B = (B - 1) - v % B`. -/
theorem sum_complement_div_mod {B v : ℕ} (hB : 2 ≤ B) (hv : v < 2 * B) :
    (2 * B - 1 - v) / B = 1 - v / B ∧ (2 * B - 1 - v) % B = B - 1 - v % B := by
  have hBpos : 0 < B := by omega
  by_cases hlt : v < B
  · have hdiv0 : v / B = 0 := Nat.div_eq_of_lt hlt
    have hmod0 : v % B = v := Nat.mod_eq_of_lt hlt
    have hvstar : 2 * B - 1 - v = (B - 1 - v) + 1 * B := by omega
    have hrem : B - 1 - v < B := by omega
    rw [hvstar, Nat.add_mul_div_right _ _ hBpos, Nat.div_eq_of_lt hrem,
      Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrem, hdiv0, hmod0]
    omega
  · have hrem : v - B < B := by omega
    have hv_eq : v = (v - B) + 1 * B := by omega
    have hvstar : 2 * B - 1 - v = B - 1 - (v - B) := by omega
    have hrem2 : B - 1 - (v - B) < B := by omega
    have hdiv1 : v / B = 1 := by
      conv_lhs => rw [hv_eq]
      rw [Nat.add_mul_div_right _ _ hBpos, Nat.div_eq_of_lt hrem]
    have hmod1 : v % B = v - B := by
      conv_lhs => rw [hv_eq]
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hrem]
    rw [hvstar, Nat.div_eq_of_lt hrem2, Nat.mod_eq_of_lt hrem2, hdiv1, hmod1]
    omega

/-- Per-phase state `(a, r, p)` of the two-run carry automaton (`tworun.py` / `tworun-1.md` §1). -/
@[ext]
structure PhaseState where
  a : ℕ
  r : ℕ
  p : ℕ
  deriving DecidableEq, Repr

/-- Validity invariant for a phase state `(a, r, p)` under overflow flag `ovBit` in base `B`. -/
def ValidPhaseState (B : ℕ) (ovBit : Bool) (st : PhaseState) : Prop :=
  st.a ≤ 1 ∧ st.r ≤ 1 ∧ (if ovBit then st.p < B else st.p = 0)

/-- Action of the complement map `φ` on a single phase state. -/
def phiPhase (B : ℕ) (ovBit : Bool) (st : PhaseState) : PhaseState where
  a := 1 - st.a
  r := 1 - st.r
  p := if ovBit then B - 1 - st.p else 0

/-- `phiPhase` preserves `ValidPhaseState` and is an involution for `B ≥ 2`. -/
theorem phiPhase_valid_and_involutive {B : ℕ} (_hB : 2 ≤ B) (ovBit : Bool) {st : PhaseState}
    (hst : ValidPhaseState B ovBit st) :
    ValidPhaseState B ovBit (phiPhase B ovBit st) ∧
    phiPhase B ovBit (phiPhase B ovBit st) = st := by
  rcases st with ⟨a, r, p⟩
  rcases hst with ⟨ha, hr, hp⟩
  dsimp only at ha hr hp
  cases ovBit
  · simp only [Bool.false_eq_true, ↓reduceIte] at hp
    refine ⟨⟨by simp [phiPhase], by simp [phiPhase], by simp [phiPhase]⟩, ?_⟩
    ext <;> dsimp [phiPhase] <;> omega
  · simp only [↓reduceIte] at hp
    refine ⟨⟨by simp [phiPhase], by simp [phiPhase], by simp [phiPhase]; omega⟩, ?_⟩
    ext <;> dsimp [phiPhase] <;> omega

/-- Action of `φ` on a `P`-phase state vector aligned with overflow pattern `ov`. -/
def phiState (B : ℕ) (ov : List Bool) (σ : List PhaseState) : List PhaseState :=
  List.zipWith (phiPhase B) ov σ

/-- Action of `φ` on a digit column pair `(lo, hi)`. -/
def phiCol (B : ℕ) (κ : ℕ × ℕ) : ℕ × ℕ :=
  (B - 1 - κ.1, B - 1 - κ.2)

/-- `phiCol` preserves `< B` bounds and is an involution whenever `κ.1 < B` and `κ.2 < B`. -/
theorem phiCol_valid_and_involutive {B : ℕ} {κ : ℕ × ℕ}
    (hκ : κ.1 < B ∧ κ.2 < B) :
    ((phiCol B κ).1 < B ∧ (phiCol B κ).2 < B) ∧ phiCol B (phiCol B κ) = κ := by
  rcases κ with ⟨x, y⟩
  rcases hκ with ⟨hx, hy⟩
  simp only [phiCol]
  refine ⟨⟨by omega, by omega⟩, ?_⟩
  ext <;> dsimp <;> omega

/-- Center-automaton node `(σ, β)` (`P` phase states and shift-register buffer of `d` columns). -/
structure CenterNode where
  σ : List PhaseState
  β : List (ℕ × ℕ)
  deriving DecidableEq, Repr

/-- Validity predicate for a phase state vector `σ` over `(B, ov)`. -/
def ValidStateVec (B : ℕ) (ov : List Bool) (σ : List PhaseState) : Prop :=
  List.Forall₂ (ValidPhaseState B) ov σ

/-- Validity predicate for a `CenterNode` over `(B, ov)`. -/
def ValidCenterNode (B : ℕ) (ov : List Bool) (nd : CenterNode) : Prop :=
  ValidStateVec B ov nd.σ ∧ ∀ κ ∈ nd.β, κ.1 < B ∧ κ.2 < B

/-- Action of `φ` on a `CenterNode`. -/
def phiCenterNode (B : ℕ) (ov : List Bool) (nd : CenterNode) : CenterNode where
  σ := phiState B ov nd.σ
  β := nd.β.map (phiCol B)

/-- `phiState` preserves `ValidStateVec` and is an involution. -/
theorem phiState_valid_and_involutive {B : ℕ} (hB : 2 ≤ B) {ov : List Bool}
    {σ : List PhaseState} (h : ValidStateVec B ov σ) :
    ValidStateVec B ov (phiState B ov σ) ∧
    phiState B ov (phiState B ov σ) = σ := by
  induction h with
  | nil => exact ⟨List.Forall₂.nil, rfl⟩
  | @cons o st os sts h0 _ ih =>
    have hst := phiPhase_valid_and_involutive hB o h0
    refine ⟨List.Forall₂.cons hst.1 ih.1, ?_⟩
    simp only [phiState, List.zipWith_cons_cons, hst.2]
    exact congrArg (st :: ·) ih.2

/-- `phiCenterNode` preserves `ValidCenterNode` and is an involution for `B ≥ 2`. -/
theorem phiCenterNode_valid_and_involutive {B : ℕ} (hB : 2 ≤ B) {ov : List Bool}
    {nd : CenterNode} (hnd : ValidCenterNode B ov nd) :
    ValidCenterNode B ov (phiCenterNode B ov nd) ∧
    phiCenterNode B ov (phiCenterNode B ov nd) = nd := by
  rcases hnd with ⟨hσ, hβ⟩
  have hst := phiState_valid_and_involutive hB hσ
  refine ⟨⟨hst.1, ?_⟩, ?_⟩
  · intro κ hκ
    simp only [phiCenterNode, List.mem_map] at hκ
    rcases hκ with ⟨q, hq, rfl⟩
    exact (phiCol_valid_and_involutive (hβ q hq)).1
  · cases nd with
    | mk σ β =>
      simp only [phiCenterNode, hst.2, List.map_map]
      congr 1
      have hmap : ∀ l : List (ℕ × ℕ), (∀ κ ∈ l, κ.1 < B ∧ κ.2 < B) →
          l.map (phiCol B ∘ phiCol B) = l := by
        intro l hl
        induction l with
        | nil => rfl
        | cons κ tl ih =>
          have hκ := (phiCol_valid_and_involutive (hl κ (List.mem_cons_self ..))).2
          simp only [List.map_cons, Function.comp_apply, hκ]
          exact congrArg (κ :: ·) (ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)))
      exact hmap β hβ

/-- Run-boundary state vector `run_state(B, ov, cin)` (`tworun.py` line 111). -/
def runState (B : ℕ) (ov : List Bool) (cin : List ℕ) : List PhaseState :=
  List.zipWith (fun o c => ⟨c, 1 - c, if o then (B - 1) * c else 0⟩) ov cin

/-- Run-boundary column `run_column(B, cin)` (`tworun.py` line 118). -/
def runColumn (B : ℕ) (cin : List ℕ) : ℕ × ℕ :=
  let u0 := (B - 1) * (1 - cin.getLastD 0)
  (u0, B - 1 - u0)

/-- Start node `S(c)` of the center automaton for `(B, ov, cin)` (`tworun.py` line 239). -/
def startCenterNode (B : ℕ) (ov : List Bool) (cin : List ℕ) : CenterNode where
  σ := runState B ov cin
  β := List.replicate ((ov.count true) / 2) (runColumn B cin)

private theorem phiState_runState (B : ℕ) :
    ∀ (os : List Bool) (cs : List ℕ), (∀ c ∈ cs, c ≤ 1) →
      phiState B os (runState B os cs) = runState B os (cs.map (1 - ·))
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | o :: os, c :: cs, hcs => by
    have hc0 : c ≤ 1 := hcs c (List.mem_cons_self ..)
    have ih := phiState_runState B os cs (fun x hx => hcs x (List.mem_cons_of_mem c hx))
    simp only [runState, List.map_cons, List.zipWith_cons_cons, phiState]
    refine congrArg₂ List.cons ?_ ih
    have hc01 : c = 0 ∨ c = 1 := by omega
    rcases hc01 with rfl | rfl <;> cases o <;> simp [phiPhase]

/-- **Center-Automaton Complement Isomorphism, Part 1 (`tworun-1.md` §1)**:
`φ` maps the start node `S(cin)` of `(B, ov, cin)` onto the start node `S(1 - cin)` of the
complementary signal `cin.map (1 - ·)`. -/
theorem startCenterNode_phi {B : ℕ} (_hB : 2 ≤ B) {ov : List Bool} {cin : List ℕ}
    (hne : cin ≠ []) (hc : ∀ c ∈ cin, c ≤ 1) :
    phiCenterNode B ov (startCenterNode B ov cin) =
      startCenterNode B ov (cin.map (1 - ·)) := by
  have hlast_pair : (cin.map (1 - ·)).getLastD 0 = 1 - cin.getLastD 0 ∧ cin.getLastD 0 ≤ 1 := by
    cases hrev : cin.reverse with
    | nil => exact (hne (List.reverse_eq_nil_iff.mp hrev)).elim
    | cons last rest =>
      have hcin : cin = rest.reverse ++ [last] := by
        have := congrArg List.reverse hrev
        simpa using this
      have hmem : last ∈ cin := by rw [hcin]; simp
      rw [hcin]
      simp [hc last hmem]
  have hcol : phiCol B (runColumn B cin) = runColumn B (cin.map (1 - ·)) := by
    rw [phiCol, runColumn, runColumn, hlast_pair.1]
    have hle := hlast_pair.2
    have h01 : cin.getLastD 0 = 0 ∨ cin.getLastD 0 = 1 := by omega
    rcases h01 with hc0 | hc1
    · rw [hc0]; simp
    · rw [hc1]; simp
  unfold phiCenterNode startCenterNode
  simp [phiState_runState B ov cin hc, hcol]

/-- Single-phase full-column relation `full_column(B, a, r, lo, hi)` (`tworun.py` line 62). -/
def fullColumn (B a r lo hi : ℕ) : List (ℕ × ℕ × ℕ × ℕ) :=
  let s := lo + hi
  ([0, 1].filter (fun b => (s + b) / B == r)).map
    (fun b => ((s + a) % B, (s + a) / B, (s + b) % B, b))

/-- Action of `φ` on a 4-tuple `(loOut, a2, hiOut, b)` returned by `fullColumn`. -/
def phiFullOut (B : ℕ) (q : ℕ × ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (B - 1 - q.1, 1 - q.2.1, B - 1 - q.2.2.1, 1 - q.2.2.2)

/-- Output range invariants of `fullColumn`. -/
theorem mem_fullColumn_bounds {B a r lo hi : ℕ} (hB : 2 ≤ B) (ha : a ≤ 1)
    (hlo : lo < B) (hhi : hi < B) {q : ℕ × ℕ × ℕ × ℕ}
    (hq : q ∈ fullColumn B a r lo hi) :
    q.1 < B ∧ q.2.1 ≤ 1 ∧ q.2.2.1 < B ∧ q.2.2.2 ≤ 1 := by
  simp only [fullColumn, List.mem_map, List.mem_filter, List.mem_cons, List.not_mem_nil,
    or_false, beq_iff_eq] at hq
  rcases hq with ⟨b, ⟨hb, _⟩, hq_eq⟩
  rw [← hq_eq]
  dsimp only
  have hBpos : 0 < B := by omega
  have hdiv : (lo + hi + a) / B ≤ 1 := by
    have hlt2 : (lo + hi + a) / B < 2 := (Nat.div_lt_iff_lt_mul hBpos).2 (by omega)
    omega
  refine ⟨Nat.mod_lt _ hBpos, hdiv, Nat.mod_lt _ hBpos, ?_⟩
  rcases hb with rfl | rfl <;> omega

/-- Forward `φ`-equivariance of `fullColumn` (`tworun-1.md` §1, Step 1). -/
theorem mem_fullColumn_phi_imp {B a r lo hi : ℕ} (hB : 2 ≤ B) (ha : a ≤ 1) (hr : r ≤ 1)
    (hlo : lo < B) (hhi : hi < B) {q : ℕ × ℕ × ℕ × ℕ}
    (hq : q ∈ fullColumn B a r lo hi) :
    phiFullOut B q ∈ fullColumn B (1 - a) (1 - r) (B - 1 - lo) (B - 1 - hi) := by
  simp only [fullColumn, List.mem_map, List.mem_filter, List.mem_cons, List.not_mem_nil,
    or_false, beq_iff_eq] at hq ⊢
  rcases hq with ⟨b, ⟨hb01, hbr⟩, hq_eq⟩
  rw [← hq_eq]
  have hsa : lo + hi + a < 2 * B := by omega
  have hsb : lo + hi + b < 2 * B := by rcases hb01 with rfl | rfl <;> omega
  have hca := sum_complement_div_mod hB hsa
  have hcb := sum_complement_div_mod hB hsb
  have hsum_a : B - 1 - lo + (B - 1 - hi) + (1 - a) = 2 * B - 1 - (lo + hi + a) := by omega
  have hsum_b : B - 1 - lo + (B - 1 - hi) + (1 - b) = 2 * B - 1 - (lo + hi + b) := by
    rcases hb01 with rfl | rfl <;> omega
  refine ⟨1 - b, ⟨by rcases hb01 with rfl | rfl <;> simp, ?_⟩, ?_⟩
  · rw [hsum_b, hcb.1, hbr]
  · simp only [phiFullOut]
    rw [hsum_a, hsum_b, hca.1, hca.2, hcb.2]

/-- Exact biconditional `φ`-equivariance of `fullColumn`. -/
theorem mem_fullColumn_phi {B a r lo hi : ℕ} (hB : 2 ≤ B) (ha : a ≤ 1) (hr : r ≤ 1)
    (hlo : lo < B) (hhi : hi < B) {q : ℕ × ℕ × ℕ × ℕ}
    (hqb : q.1 < B ∧ q.2.1 ≤ 1 ∧ q.2.2.1 < B ∧ q.2.2.2 ≤ 1) :
    q ∈ fullColumn B a r lo hi ↔
      phiFullOut B q ∈ fullColumn B (1 - a) (1 - r) (B - 1 - lo) (B - 1 - hi) := by
  constructor
  · exact mem_fullColumn_phi_imp hB ha hr hlo hhi
  · intro h
    have h2 := mem_fullColumn_phi_imp hB (by omega) (by omega) (by omega) (by omega) h
    have ha' : 1 - (1 - a) = a := by omega
    have hr' : 1 - (1 - r) = r := by omega
    have hlo' : B - 1 - (B - 1 - lo) = lo := by omega
    have hhi' : B - 1 - (B - 1 - hi) = hi := by omega
    have hq' : phiFullOut B (phiFullOut B q) = q := by
      rcases q with ⟨x1, x2, x3, x4⟩
      rcases hqb with ⟨hx1, hx2, hx3, hx4⟩
      dsimp only at hx1 hx2 hx3 hx4
      simp only [phiFullOut, Prod.mk.injEq]
      exact ⟨by omega, by omega, by omega, by omega⟩
    rwa [ha', hr', hlo', hhi', hq'] at h2

/-- Multi-phase column transition `advance(B, ov, σ, (lo, hi))` (`tworun.py` line 72). -/
def advanceAux (B : ℕ) : List Bool → List PhaseState → ℕ → ℕ →
    List (List PhaseState × (ℕ × ℕ))
  | [], [], lo, hi => [([], (lo, hi))]
  | o :: os, st :: sts, lo, hi =>
    (fullColumn B st.a st.r lo hi).flatMap (fun q =>
      let nxt := if o then st.p else q.2.2.1
      let st' : PhaseState := ⟨q.2.1, q.2.2.2, if o then q.2.2.1 else 0⟩
      (advanceAux B os sts q.1 nxt).map (fun res => (st' :: res.1, res.2)))
  | _, _, _, _ => []

/-- `advanceAux` outputs valid successor state vectors and columns `< B`. -/
theorem mem_advanceAux_valid {B : ℕ} (hB : 2 ≤ B) :
    ∀ (ov : List Bool) (σ : List PhaseState) (lo hi : ℕ),
      ValidStateVec B ov σ → lo < B → hi < B →
      ∀ res ∈ advanceAux B ov σ lo hi,
        ValidStateVec B ov res.1 ∧ res.2.1 < B ∧ res.2.2 < B
  | [], [], lo, hi, _, hlo, hhi, res, hres => by
    simp only [advanceAux, List.mem_singleton] at hres
    subst hres
    exact ⟨List.Forall₂.nil, hlo, hhi⟩
  | o :: os, st :: sts, lo, hi, List.Forall₂.cons h0 hrest, hlo, hhi, res, hres => by
    simp only [advanceAux, List.mem_flatMap, List.mem_map] at hres
    rcases hres with ⟨q, hq, ⟨tailRes, htail, rfl⟩⟩
    have hqb := mem_fullColumn_bounds hB h0.1 hlo hhi hq
    have hnxt : (if o then st.p else q.2.2.1) < B := by
      cases o
      · simpa using hqb.2.2.1
      · simpa using h0.2.2
    have ih := mem_advanceAux_valid hB os sts q.1 (if o then st.p else q.2.2.1)
      hrest hqb.1 hnxt tailRes htail
    refine ⟨List.Forall₂.cons ?_ ih.1, ih.2⟩
    refine ⟨hqb.2.1, hqb.2.2.2, ?_⟩
    cases o <;> simp [hqb.2.2.1]

/-- Forward `φ`-equivariance of `advanceAux` (`tworun-1.md` §1, Step 2). -/
theorem mem_advanceAux_phi_imp {B : ℕ} (hB : 2 ≤ B) :
    ∀ (ov : List Bool) (σ : List PhaseState) (lo hi : ℕ),
      ValidStateVec B ov σ → lo < B → hi < B →
      ∀ res ∈ advanceAux B ov σ lo hi,
        (phiState B ov res.1, phiCol B res.2) ∈
          advanceAux B ov (phiState B ov σ) (B - 1 - lo) (B - 1 - hi)
  | [], [], lo, hi, _, _, _, res, hres => by
    simp only [advanceAux, List.mem_singleton] at hres
    subst hres
    simp [advanceAux, phiState, phiCol]
  | o :: os, st :: sts, lo, hi, List.Forall₂.cons h0 hrest, hlo, hhi, res, hres => by
    simp only [advanceAux, List.mem_flatMap, List.mem_map] at hres
    rcases hres with ⟨q, hq, ⟨tailRes, htail, rfl⟩⟩
    have hqb := mem_fullColumn_bounds hB h0.1 hlo hhi hq
    have hq_phi := mem_fullColumn_phi_imp hB h0.1 h0.2.1 hlo hhi hq
    have hnxt : (if o then st.p else q.2.2.1) < B := by
      cases o
      · simpa using hqb.2.2.1
      · simpa using h0.2.2
    have ih := mem_advanceAux_phi_imp hB os sts q.1 (if o then st.p else q.2.2.1)
      hrest hqb.1 hnxt tailRes htail
    simp only [phiState, List.zipWith_cons_cons, advanceAux, List.mem_flatMap, List.mem_map]
    refine ⟨phiFullOut B q, ?_, ⟨(phiState B os tailRes.1, phiCol B tailRes.2), ?_, ?_⟩⟩
    · simpa [phiPhase] using hq_phi
    · have hnxt_eq : (if o then (phiPhase B o st).p else (phiFullOut B q).2.2.1) =
          B - 1 - (if o then st.p else q.2.2.1) := by
        cases o <;> simp [phiPhase, phiFullOut]
      rw [hnxt_eq]
      exact ih
    · cases o <;> simp [phiPhase, phiFullOut, phiState]

/-- Transition relation `(σ, β) → (σ', β')` by column `κ` in the center automaton (`tworun-1.md` §1). -/
def centerEdge (B : ℕ) (ov : List Bool) (nd : CenterNode) (κ : ℕ × ℕ) (nd' : CenterNode) : Prop :=
  κ.1 < B ∧ κ.2 < B ∧
  ∃ hd tl, nd.β = hd :: tl ∧ (nd'.σ, hd) ∈ advanceAux B ov nd.σ κ.1 κ.2 ∧ nd'.β = tl ++ [κ]

/-- Every `centerEdge` transition from a `ValidCenterNode` produces a `ValidCenterNode`. -/
theorem centerEdge_valid {B : ℕ} (hB : 2 ≤ B) {ov : List Bool} {nd nd' : CenterNode} {κ : ℕ × ℕ}
    (hnd : ValidCenterNode B ov nd) (hedge : centerEdge B ov nd κ nd') :
    ValidCenterNode B ov nd' := by
  rcases hedge with ⟨hκ1, hκ2, hd, tl, hβ, hadv, hβ'⟩
  have hv := mem_advanceAux_valid hB ov nd.σ κ.1 κ.2 hnd.1 hκ1 hκ2 (nd'.σ, hd) hadv
  refine ⟨hv.1, ?_⟩
  rw [hβ']
  intro q hq
  simp only [List.mem_append, List.mem_singleton] at hq
  rcases hq with hq | rfl
  · exact hnd.2 q (by rw [hβ]; exact List.mem_cons_of_mem hd hq)
  · exact ⟨hκ1, hκ2⟩

/-- **Center-Automaton Complement Isomorphism, Part 2 (`tworun-1.md` §1)**:
for any valid nodes `nd, nd'` and column `κ` (`κ.1 < B`, `κ.2 < B`), `(nd, κ) → nd'` holds in
the center automaton iff `(φ(nd), φ(κ)) → φ(nd')` holds. -/
theorem centerEdge_phi {B : ℕ} (hB : 2 ≤ B) {ov : List Bool} {nd nd' : CenterNode} {κ : ℕ × ℕ}
    (hnd : ValidCenterNode B ov nd) (hnd' : ValidCenterNode B ov nd')
    (hκ : κ.1 < B ∧ κ.2 < B) :
    centerEdge B ov nd κ nd' ↔
      centerEdge B ov (phiCenterNode B ov nd) (phiCol B κ) (phiCenterNode B ov nd') := by
  have fwd : ∀ {n1 n2 : CenterNode} {k : ℕ × ℕ},
      ValidCenterNode B ov n1 → (k.1 < B ∧ k.2 < B) → centerEdge B ov n1 k n2 →
      centerEdge B ov (phiCenterNode B ov n1) (phiCol B k) (phiCenterNode B ov n2) := by
    intro n1 n2 k hn1 hk he
    rcases he with ⟨hk1, hk2, hd, tl, hβ, hadv, hβ'⟩
    have hk_phi := (phiCol_valid_and_involutive hk).1
    refine ⟨hk_phi.1, hk_phi.2, phiCol B hd, tl.map (phiCol B), ?_, ?_, ?_⟩
    · simp [phiCenterNode, hβ]
    · simpa [phiCenterNode, phiCol] using
        mem_advanceAux_phi_imp hB ov n1.σ k.1 k.2 hn1.1 hk1 hk2 (n2.σ, hd) hadv
    · simp [phiCenterNode, hβ']
  constructor
  · exact fwd hnd hκ
  · intro he
    have hnd_p := phiCenterNode_valid_and_involutive hB hnd
    have hnd'_p := phiCenterNode_valid_and_involutive hB hnd'
    have hκ_p := phiCol_valid_and_involutive hκ
    have hback := fwd hnd_p.1 hκ_p.1 he
    rwa [hnd_p.2, hnd'_p.2, hκ_p.2] at hback

/-- Multi-step path in the center automaton reading column list `cols`. -/
inductive CenterPath (B : ℕ) (ov : List Bool) :
    CenterNode → List (ℕ × ℕ) → CenterNode → Prop
  | nil (nd : CenterNode) : CenterPath B ov nd [] nd
  | cons {nd₁ nd₂ nd₃ : CenterNode} {κ : ℕ × ℕ} {cols : List (ℕ × ℕ)} :
      centerEdge B ov nd₁ κ nd₂ →
      CenterPath B ov nd₂ cols nd₃ →
      CenterPath B ov nd₁ (κ :: cols) nd₃

/-- **BFS Depth / Path Isomorphism**: `φ` maps length-`k` paths in the center automaton of `cin`
bijectively onto length-`k` paths in the center automaton of `1 - cin`. -/
theorem centerPath_phi {B : ℕ} (hB : 2 ≤ B) {ov : List Bool} {nd nd' : CenterNode}
    {cols : List (ℕ × ℕ)} (hnd : ValidCenterNode B ov nd) (hnd' : ValidCenterNode B ov nd')
    (hcols : ∀ κ ∈ cols, κ.1 < B ∧ κ.2 < B) :
    CenterPath B ov nd cols nd' ↔
      CenterPath B ov (phiCenterNode B ov nd) (cols.map (phiCol B)) (phiCenterNode B ov nd') := by
  have fwd : ∀ {n1 n3 : CenterNode} {cs : List (ℕ × ℕ)},
      ValidCenterNode B ov n1 → CenterPath B ov n1 cs n3 →
      CenterPath B ov (phiCenterNode B ov n1) (cs.map (phiCol B)) (phiCenterNode B ov n3) := by
    intro n1 n3 cs hn1 hp
    induction hp with
    | nil n => exact CenterPath.nil _
    | @cons na nb nc κ rest he _ ih =>
      have hnb := centerEdge_valid hB hn1 he
      have he_phi := (centerEdge_phi hB hn1 hnb ⟨he.1, he.2.1⟩).mp he
      exact CenterPath.cons he_phi (ih hnb)
  have hcols_inv : ∀ (l : List (ℕ × ℕ)), (∀ κ ∈ l, κ.1 < B ∧ κ.2 < B) →
      (l.map (phiCol B)).map (phiCol B) = l := by
    intro l hl
    induction l with
    | nil => rfl
    | cons κ tl ih =>
      have hκ := (phiCol_valid_and_involutive (hl κ (List.mem_cons_self ..))).2
      simp only [List.map_cons, hκ]
      exact congrArg (κ :: ·) (ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)))
  constructor
  · exact fwd hnd
  · intro hp
    have hnd_p := phiCenterNode_valid_and_involutive hB hnd
    have hnd'_p := phiCenterNode_valid_and_involutive hB hnd'
    have hback := fwd hnd_p.1 hp
    rwa [hnd_p.2, hnd'_p.2, hcols_inv cols hcols] at hback

/-- Phase role at closing layer `layer` given `half = odd + o_t` (`tworun.py` line 158). -/
inductive PhaseKind where
  | full | mid | close | none
  deriving DecidableEq, Repr

/-- Compute `phase_kind(layer, half)` (`tworun.py` line 158). -/
def phaseKind (layer half : ℕ) : PhaseKind :=
  if layer < half / 2 then .full
  else if layer = half / 2 then (if half % 2 = 1 then .mid else .close)
  else .none

/-- End-of-layer check `check_xp` (`tworun.py` line 218). -/
def checkXp (i halfP : ℕ) (lastOv : Bool) (buf : List (ℕ × ℕ)) (middle : ℕ)
    (loPart hiPart : Option ℕ) : Bool :=
  match phaseKind i halfP with
  | .full =>
    match buf[i]?, loPart, hiPart with
    | some (blo, bhi), some lo, some hi => (lo == blo) && (hi == bhi)
    | _, _, _ => false
  | .mid =>
    match (if lastOv then hiPart else loPart) with
    | some dig => dig == middle
    | none => false
  | _ => true

/-- Single-layer phase sweep of `closes` (`tworun.py` line 186), returning all valid updated
`(ov, PhaseState)` lists passing `checkXp`. -/
def closesPhase (B : ℕ) (buf : List (ℕ × ℕ)) (middle i : ℕ) (isFirst prevOv : Bool)
    (curHalf : ℕ) (loPart hiPart : Option ℕ) :
    List (Bool × PhaseState) → List (List (Bool × PhaseState))
  | [] =>
    if checkXp i curHalf prevOv buf middle loPart hiPart then [[]] else []
  | (o, st) :: rest =>
    let kind := phaseKind i curHalf
    let loIn : Option ℕ :=
      if isFirst then (if kind == .mid then some middle else none) else loPart
    let hiIn : Option ℕ :=
      if isFirst then none else hiPart
    let nxtHalf := curHalf + if o then 1 else 0
    match kind with
    | .none =>
      (closesPhase B buf middle i false o nxtHalf none none rest).map ((o, st) :: ·)
    | .close =>
      if st.a != st.r then []
      else
        let nxtHi := if o then some st.p else none
        (closesPhase B buf middle i false o nxtHalf none nxtHi rest).map ((o, st) :: ·)
    | .mid =>
      let digOpt := if isFirst || !prevOv then loIn else hiIn
      match digOpt with
      | none => []
      | some dig =>
        let v := 2 * dig + st.a
        if v / B != st.r then []
        else
          let nxtHi := if o then some st.p else none
          (closesPhase B buf middle i false o nxtHalf (some (v % B)) nxtHi rest).map
            ((o, st) :: ·)
    | .full =>
      match loIn, hiIn with
      | some lo, some hi =>
        (fullColumn B st.a st.r lo hi).flatMap (fun q =>
          let nxt := if o then st.p else q.2.2.1
          let st' : PhaseState := ⟨q.2.1, q.2.2.2, if o then q.2.2.1 else 0⟩
          (closesPhase B buf middle i false o nxtHalf (some q.1) (some nxt) rest).map
            ((o, st') :: ·))
      | _, _ => []

/-- Multi-layer recursion of `closes` (`tworun.py` line 180). -/
def closesLayer (B : ℕ) (buf : List (ℕ × ℕ)) (odd middle : ℕ) :
    ℕ → ℕ → List (Bool × PhaseState) → Bool
  | 0, _, _ => true
  | rem + 1, i, pairs =>
    (closesPhase B buf middle i true false odd none none pairs).any
      (closesLayer B buf odd middle rem (i + 1))

/-- Center closure test `closes(B, ov, nd, odd, middle)` (`tworun.py` line 167). -/
def closes (B : ℕ) (ov : List Bool) (nd : CenterNode) (odd middle : ℕ) : Bool :=
  closesLayer B nd.β odd middle ((ov.count true) / 2 + 1) 0 (List.zip ov nd.σ)

private def phiPairs (B : ℕ) (pairs : List (Bool × PhaseState)) : List (Bool × PhaseState) :=
  pairs.map (fun p => (p.1, phiPhase B p.1 p.2))

private def ValidPairs (B : ℕ) (pairs : List (Bool × PhaseState)) : Prop :=
  ∀ p ∈ pairs, ValidPhaseState B p.1 p.2

private def ValidOpt (B : ℕ) (opt : Option ℕ) : Prop :=
  ∀ x, opt = some x → x < B

private theorem validPairs_zip {B : ℕ} {ov : List Bool} {σ : List PhaseState}
    (h : ValidStateVec B ov σ) : ValidPairs B (List.zip ov σ) := by
  induction h with
  | nil => intro p hp; simp at hp
  | cons h0 _ ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact h0
    · exact ih p hp'

private theorem zip_phiState (B : ℕ) :
    ∀ (os : List Bool) (sts : List PhaseState),
      List.zip os (phiState B os sts) = phiPairs B (List.zip os sts)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | o :: os, st :: sts => by
    simp only [phiState, phiPairs, List.zipWith_cons_cons, List.zip_cons_cons, List.map_cons]
    exact congrArg ((o, phiPhase B o st) :: ·) (zip_phiState B os sts)

private theorem checkXp_phi {B i halfP : ℕ} (_hB : 2 ≤ B) (lastOv : Bool)
    {buf : List (ℕ × ℕ)} (hbuf : ∀ κ ∈ buf, κ.1 < B ∧ κ.2 < B)
    {middle : ℕ} (hmid : middle < B) {loPart hiPart : Option ℕ}
    (hlo : ValidOpt B loPart) (hhi : ValidOpt B hiPart) :
    checkXp i halfP lastOv (buf.map (phiCol B)) (B - 1 - middle)
      (loPart.map (B - 1 - ·)) (hiPart.map (B - 1 - ·)) =
      checkXp i halfP lastOv buf middle loPart hiPart := by
  unfold checkXp
  cases phaseKind i halfP with
  | full =>
    cases hbi : buf[i]? with
    | none => simp [hbi]
    | some bpair =>
      rcases bpair with ⟨blo, bhi⟩
      have hb_mem : (blo, bhi) ∈ buf := List.mem_of_getElem? hbi
      have hb_lt := hbuf (blo, bhi) hb_mem
      simp only [List.getElem?_map, hbi, Option.map_some, phiCol]
      cases loPart with
      | none => simp
      | some lo =>
        cases hiPart with
        | none => simp
        | some hi =>
          have hlo' : lo < B := hlo lo rfl
          have hhi' : hi < B := hhi hi rfl
          simp only [Option.map_some, Bool.beq_eq_decide_eq]
          have e1 : (B - 1 - lo = B - 1 - blo) ↔ (lo = blo) := by omega
          have e2 : (B - 1 - hi = B - 1 - bhi) ↔ (hi = bhi) := by omega
          simp [e1, e2]
  | mid =>
    cases lastOv
    · cases loPart with
      | none => simp
      | some dig =>
        have hdig : dig < B := hlo dig rfl
        have e : (B - 1 - dig = B - 1 - middle) ↔ (dig = middle) := by omega
        simp [e]
    · cases hiPart with
      | none => simp
      | some dig =>
        have hdig : dig < B := hhi dig rfl
        have e : (B - 1 - dig = B - 1 - middle) ↔ (dig = middle) := by omega
        simp [e]
  | close => rfl
  | none => rfl

private theorem mem_closesPhase_valid {B : ℕ} (hB : 2 ≤ B) {buf : List (ℕ × ℕ)}
    {middle : ℕ} (hmid : middle < B) :
    ∀ (i : ℕ) (isFirst prevOv : Bool) (curHalf : ℕ) (loPart hiPart : Option ℕ)
      (pairs : List (Bool × PhaseState)),
      ValidPairs B pairs → ValidOpt B loPart → ValidOpt B hiPart →
      ∀ out ∈ closesPhase B buf middle i isFirst prevOv curHalf loPart hiPart pairs,
        ValidPairs B out
  | i, _, prevOv, curHalf, loPart, hiPart, [], _, _, _, out, hout => by
    unfold closesPhase at hout
    by_cases hchk : checkXp i curHalf prevOv buf middle loPart hiPart = true
    · simp only [hchk, ↓reduceIte, List.mem_singleton] at hout
      subst hout
      intro p hp; simp at hp
    · simp [hchk] at hout
  | i, isFirst, prevOv, curHalf, loPart, hiPart, (o, ⟨a, r, p⟩) :: rest, hpairs, hlo, hhi, out, hout => by
    have h0 : ValidPhaseState B o ⟨a, r, p⟩ := hpairs (o, ⟨a, r, p⟩) (List.mem_cons_self ..)
    have hrest : ValidPairs B rest := fun q hq => hpairs q (List.mem_cons_of_mem _ hq)
    have hBpos : 0 < B := by omega
    unfold closesPhase at hout
    dsimp only at hout
    cases hkind : phaseKind i curHalf with
    | none =>
      rw [hkind] at hout
      simp only [List.mem_map] at hout
      rcases hout with ⟨tl, htl, rfl⟩
      have ih := mem_closesPhase_valid hB hmid i false o (curHalf + if o then 1 else 0)
        none none rest hrest (fun _ h => by simp at h) (fun _ h => by simp at h) tl htl
      intro q hq
      rcases List.mem_cons.mp hq with rfl | hq'
      · exact h0
      · exact ih q hq'
    | close =>
      rw [hkind] at hout
      by_cases har : (a != r) = true
      · simp [har] at hout
      · simp only [har, Bool.false_eq_true, ↓reduceIte, List.mem_map] at hout
        rcases hout with ⟨tl, htl, rfl⟩
        have hnxtHi : ValidOpt B (if o then some p else none) := by
          intro x hx; cases o <;> simp at hx; subst hx; exact h0.2.2
        have ih := mem_closesPhase_valid hB hmid i false o (curHalf + if o then 1 else 0)
          none (if o then some p else none) rest hrest
          (fun _ h => by simp at h) hnxtHi tl htl
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq'
        · exact h0
        · exact ih q hq'
    | mid =>
      rw [hkind] at hout
      have hm_eq : (PhaseKind.mid == .mid) = true := rfl
      simp only [hm_eq, ↓reduceIte] at hout
      cases hdig : (if isFirst || !prevOv then
          (if isFirst then some middle else loPart)
        else (if isFirst then none else hiPart)) with
      | none => rw [hdig] at hout; simp at hout
      | some dig =>
        rw [hdig] at hout
        dsimp only at hout
        by_cases hv : ((2 * dig + a) / B != r) = true
        · simp [hv] at hout
        · simp only [hv, Bool.false_eq_true, ↓reduceIte, List.mem_map] at hout
          rcases hout with ⟨tl, htl, rfl⟩
          have hnxtLo : ValidOpt B (some ((2 * dig + a) % B)) := by
            intro x hx; simp at hx; subst hx; exact Nat.mod_lt _ hBpos
          have hnxtHi : ValidOpt B (if o then some p else none) := by
            intro x hx; cases o <;> simp at hx; subst hx; exact h0.2.2
          have ih := mem_closesPhase_valid hB hmid i false o (curHalf + if o then 1 else 0)
            (some ((2 * dig + a) % B)) (if o then some p else none)
            rest hrest hnxtLo hnxtHi tl htl
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq'
          · exact h0
          · exact ih q hq'
    | full =>
      rw [hkind] at hout
      have hf_eq : (PhaseKind.full == .mid) = false := rfl
      simp only [hf_eq, Bool.false_eq_true, ↓reduceIte] at hout
      cases isFirst
      · simp only [Bool.false_eq_true, ↓reduceIte] at hout
        cases loPart with
        | none => simp at hout
        | some lo =>
          cases hiPart with
          | none => simp at hout
          | some hi =>
            simp only [List.mem_flatMap, List.mem_map] at hout
            rcases hout with ⟨q, hq, ⟨tl, htl, rfl⟩⟩
            have hqb := mem_fullColumn_bounds hB h0.1 (hlo lo rfl) (hhi hi rfl) hq
            have hnxt : (if o then p else q.2.2.1) < B := by
              cases o
              · simpa using hqb.2.2.1
              · simpa using h0.2.2
            have ih := mem_closesPhase_valid hB hmid i false o (curHalf + if o then 1 else 0)
              (some q.1) (some (if o then p else q.2.2.1)) rest hrest
              (fun x hx => by simp at hx; subst hx; exact hqb.1)
              (fun x hx => by simp at hx; subst hx; exact hnxt) tl htl
            intro pair hp
            rcases List.mem_cons.mp hp with rfl | hp'
            · refine ⟨hqb.2.1, hqb.2.2.2, ?_⟩
              cases o <;> simp [hqb.2.2.1]
            · exact ih pair hp'
      · simp at hout

private theorem mem_closesPhase_phi_imp {B : ℕ} (hB : 2 ≤ B) {buf : List (ℕ × ℕ)}
    (hbuf : ∀ κ ∈ buf, κ.1 < B ∧ κ.2 < B) {middle : ℕ} (hmid : middle < B) :
    ∀ (i : ℕ) (isFirst prevOv : Bool) (curHalf : ℕ) (loPart hiPart : Option ℕ)
      (pairs : List (Bool × PhaseState)),
      ValidPairs B pairs → ValidOpt B loPart → ValidOpt B hiPart →
      ∀ out ∈ closesPhase B buf middle i isFirst prevOv curHalf loPart hiPart pairs,
        phiPairs B out ∈ closesPhase B (buf.map (phiCol B)) (B - 1 - middle) i isFirst prevOv
          curHalf (loPart.map (B - 1 - ·)) (hiPart.map (B - 1 - ·)) (phiPairs B pairs)
  | i, _, prevOv, curHalf, loPart, hiPart, [], _, hlo, hhi, out, hout => by
    simp only [phiPairs, List.map_nil, closesPhase] at hout ⊢
    rw [checkXp_phi hB prevOv hbuf hmid hlo hhi]
    by_cases hchk : checkXp i curHalf prevOv buf middle loPart hiPart = true
    · simp only [hchk, ↓reduceIte, List.mem_singleton] at hout ⊢
      subst hout
      rfl
    · simp [hchk] at hout
  | i, isFirst, prevOv, curHalf, loPart, hiPart, (o, ⟨a, r, p⟩) :: rest, hpairs, hlo, hhi, out, hout => by
    have h0 : ValidPhaseState B o ⟨a, r, p⟩ := hpairs (o, ⟨a, r, p⟩) (List.mem_cons_self ..)
    have hrest : ValidPairs B rest := fun q hq => hpairs q (List.mem_cons_of_mem _ hq)
    have hBpos : 0 < B := by omega
    rcases h0 with ⟨ha, hr, hp⟩
    dsimp only at ha hr hp
    unfold closesPhase at hout
    dsimp only at hout
    simp only [phiPairs, List.map_cons]
    unfold closesPhase
    dsimp only
    cases hkind : phaseKind i curHalf with
    | none =>
      rw [hkind] at hout
      dsimp only
      simp only [List.mem_map] at hout ⊢
      rcases hout with ⟨tl, htl, rfl⟩
      exact ⟨phiPairs B tl,
        mem_closesPhase_phi_imp hB hbuf hmid i false o (curHalf + if o then 1 else 0)
          none none rest hrest (fun _ h => by simp at h) (fun _ h => by simp at h) tl htl, rfl⟩
    | close =>
      rw [hkind] at hout
      dsimp only
      have har_eq : ((phiPhase B o ⟨a, r, p⟩).a != (phiPhase B o ⟨a, r, p⟩).r) = (a != r) := by
        have ha01 : a = 0 ∨ a = 1 := by omega
        have hr01 : r = 0 ∨ r = 1 := by omega
        rcases ha01 with rfl | rfl <;> rcases hr01 with rfl | rfl <;> rfl
      rw [har_eq]
      by_cases har : (a != r) = true
      · simp [har] at hout
      · simp only [har, Bool.false_eq_true, ↓reduceIte, List.mem_map] at hout ⊢
        rcases hout with ⟨tl, htl, rfl⟩
        have hnxtHi : ValidOpt B (if o then some p else none) := by
          intro x hx; cases o <;> simp at hx; subst hx; exact hp
        have hmap_hi : (if o then some (phiPhase B o ⟨a, r, p⟩).p else none) =
            (if o then some p else none).map (B - 1 - ·) := by
          cases o <;> simp [phiPhase]
        rw [hmap_hi]
        exact ⟨phiPairs B tl,
          mem_closesPhase_phi_imp hB hbuf hmid i false o (curHalf + if o then 1 else 0)
            none (if o then some p else none) rest hrest
            (fun _ h => by simp at h) hnxtHi tl htl, rfl⟩
    | mid =>
      rw [hkind] at hout
      dsimp only
      have hm_eq : (PhaseKind.mid == .mid) = true := rfl
      simp only [hm_eq, ↓reduceIte] at hout ⊢
      have hdig_map :
          (if isFirst || !prevOv then
            if isFirst then some (B - 1 - middle) else loPart.map (B - 1 - ·)
          else
            if isFirst then none else hiPart.map (B - 1 - ·)) =
          (if isFirst || !prevOv then
            if isFirst then some middle else loPart
          else
            if isFirst then none else hiPart).map (B - 1 - ·) := by
        cases isFirst <;> cases prevOv <;> simp
      rw [hdig_map]
      cases hdig : (if isFirst || !prevOv then (if isFirst then some middle else loPart)
          else (if isFirst then none else hiPart)) with
      | none => rw [hdig] at hout; simp at hout
      | some dig =>
        rw [hdig] at hout
        have hdig_lt : dig < B := by
          cases isFirst <;> cases prevOv <;> simp at hdig
          · exact hlo dig hdig
          · exact hhi dig hdig
          · subst hdig; exact hmid
          · subst hdig; exact hmid
        simp only [Option.map_some] at hout ⊢
        have hv_lt : 2 * dig + a < 2 * B := by omega
        have hsum := sum_complement_div_mod hB hv_lt
        have hvstar : 2 * (B - 1 - dig) + (phiPhase B o ⟨a, r, p⟩).a = 2 * B - 1 - (2 * dig + a) := by
          dsimp [phiPhase]; omega
        have hdiv_eq : ((2 * (B - 1 - dig) + (phiPhase B o ⟨a, r, p⟩).a) / B !=
            (phiPhase B o ⟨a, r, p⟩).r) = ((2 * dig + a) / B != r) := by
          rw [hvstar, hsum.1]
          dsimp [phiPhase]
          have hq_le : (2 * dig + a) / B ≤ 1 := by
            have : (2 * dig + a) / B < 2 := (Nat.div_lt_iff_lt_mul hBpos).2 hv_lt
            omega
          generalize (2 * dig + a) / B = qv at hq_le ⊢
          have hq01 : qv = 0 ∨ qv = 1 := by omega
          have hr01 : r = 0 ∨ r = 1 := by omega
          rcases hq01 with rfl | rfl <;> rcases hr01 with rfl | rfl <;> rfl
        rw [hdiv_eq]
        by_cases hvbad : ((2 * dig + a) / B != r) = true
        · simp [hvbad] at hout
        · simp only [hvbad, Bool.false_eq_true, ↓reduceIte, List.mem_map] at hout ⊢
          rcases hout with ⟨tl, htl, rfl⟩
          have hmod_eq : some ((2 * (B - 1 - dig) + (phiPhase B o ⟨a, r, p⟩).a) % B) =
              (some ((2 * dig + a) % B)).map (B - 1 - ·) := by
            rw [hvstar, hsum.2]; rfl
          have hmap_hi : (if o then some (phiPhase B o ⟨a, r, p⟩).p else none) =
              (if o then some p else none).map (B - 1 - ·) := by
            cases o <;> simp [phiPhase]
          rw [hmod_eq, hmap_hi]
          have hnxtLo : ValidOpt B (some ((2 * dig + a) % B)) := by
            intro x hx; simp at hx; subst hx; exact Nat.mod_lt _ hBpos
          have hnxtHi : ValidOpt B (if o then some p else none) := by
            intro x hx; cases o <;> simp at hx; subst hx; exact hp
          exact ⟨phiPairs B tl,
            mem_closesPhase_phi_imp hB hbuf hmid i false o (curHalf + if o then 1 else 0)
              (some ((2 * dig + a) % B)) (if o then some p else none)
              rest hrest hnxtLo hnxtHi tl htl,
            rfl⟩
    | full =>
      rw [hkind] at hout
      dsimp only
      have hf_eq : (PhaseKind.full == .mid) = false := rfl
      simp only [hf_eq, Bool.false_eq_true, ↓reduceIte] at hout ⊢
      cases isFirst
      · simp only [Bool.false_eq_true, ↓reduceIte] at hout ⊢
        cases loPart with
        | none => simp at hout
        | some lo =>
          cases hiPart with
          | none => simp at hout
          | some hi =>
            simp only [Option.map_some, List.mem_flatMap, List.mem_map] at hout ⊢
            rcases hout with ⟨q, hq, ⟨tl, htl, rfl⟩⟩
            have hlo' : lo < B := hlo lo rfl
            have hhi' : hi < B := hhi hi rfl
            have hqb := mem_fullColumn_bounds hB ha hlo' hhi' hq
            have hq_phi := mem_fullColumn_phi_imp hB ha hr hlo' hhi' hq
            have hnxt : (if o then p else q.2.2.1) < B := by
              cases o
              · simpa using hqb.2.2.1
              · simpa using hp
            refine ⟨phiFullOut B q, by simpa [phiPhase] using hq_phi, ⟨phiPairs B tl, ?_, ?_⟩⟩
            · have hnxt_map :
                  some (if o then (phiPhase B o ⟨a, r, p⟩).p else (phiFullOut B q).2.2.1) =
                  (some (if o then p else q.2.2.1)).map (B - 1 - ·) := by
                cases o <;> simp [phiPhase, phiFullOut]
              rw [hnxt_map]
              exact mem_closesPhase_phi_imp hB hbuf hmid i false o (curHalf + if o then 1 else 0)
                (some q.1) (some (if o then p else q.2.2.1)) rest hrest
                (fun x hx => by simp at hx; subst hx; exact hqb.1)
                (fun x hx => by simp at hx; subst hx; exact hnxt) tl htl
            · cases o <;> simp [phiPhase, phiFullOut, phiPairs]
      · simp at hout

private theorem closesLayer_phi_imp {B : ℕ} (hB : 2 ≤ B) {buf : List (ℕ × ℕ)}
    (hbuf : ∀ κ ∈ buf, κ.1 < B ∧ κ.2 < B) (odd : ℕ) {middle : ℕ} (hmid : middle < B) :
    ∀ (rem i : ℕ) (pairs : List (Bool × PhaseState)),
      ValidPairs B pairs →
      closesLayer B buf odd middle rem i pairs = true →
      closesLayer B (buf.map (phiCol B)) odd (B - 1 - middle) rem i (phiPairs B pairs) = true
  | 0, _, _, _, _ => rfl
  | rem + 1, i, pairs, hpairs, hcl => by
    simp only [closesLayer, List.any_eq_true] at hcl ⊢
    rcases hcl with ⟨nxt, hnxt, hrem⟩
    have hnxt_val := mem_closesPhase_valid hB hmid i true false odd none none pairs hpairs
      (fun _ h => by simp at h) (fun _ h => by simp at h) nxt hnxt
    have hnxt_phi := mem_closesPhase_phi_imp hB hbuf hmid i true false odd none none pairs hpairs
      (fun _ h => by simp at h) (fun _ h => by simp at h) nxt hnxt
    exact ⟨phiPairs B nxt, hnxt_phi, closesLayer_phi_imp hB hbuf odd hmid rem (i + 1) nxt hnxt_val hrem⟩

/-- **Center-Automaton Complement Isomorphism, Part 3 (`tworun-1.md` §1)**:
for any valid center node `nd` and middle digit `middle < B`, `closes` accepts `(nd, odd, middle)`
iff it accepts `(φ(nd), odd, B - 1 - middle)`. -/
theorem closes_phi {B : ℕ} (hB : 2 ≤ B) {ov : List Bool} {nd : CenterNode}
    (hnd : ValidCenterNode B ov nd) (odd : ℕ) {middle : ℕ} (hmid : middle < B) :
    closes B ov (phiCenterNode B ov nd) odd (B - 1 - middle) =
      closes B ov nd odd middle := by
  have hzip_val : ValidPairs B (List.zip ov nd.σ) := validPairs_zip hnd.1
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    have hnd_p := phiCenterNode_valid_and_involutive hB hnd
    have hmid_p : B - 1 - middle < B := by omega
    have hmid_inv : B - 1 - (B - 1 - middle) = middle := by omega
    have hzip_val_p : ValidPairs B (List.zip ov (phiCenterNode B ov nd).σ) :=
      validPairs_zip hnd_p.1.1
    have hback := closesLayer_phi_imp hB hnd_p.1.2 odd hmid_p
      ((ov.count true) / 2 + 1) 0 (List.zip ov (phiCenterNode B ov nd).σ) hzip_val_p h
    unfold closes
    have hrew : phiCenterNode B ov (phiCenterNode B ov nd) = nd := hnd_p.2
    have hβ_inv : ((phiCenterNode B ov nd).β).map (phiCol B) = nd.β :=
      congrArg CenterNode.β hrew
    have hσ_inv : phiPairs B (List.zip ov (phiCenterNode B ov nd).σ) = List.zip ov nd.σ := by
      rw [← zip_phiState B]
      exact congrArg (List.zip ov) (congrArg CenterNode.σ hrew)
    rwa [hβ_inv, hmid_inv, hσ_inv] at hback
  · intro h
    unfold closes at h ⊢
    simp only [phiCenterNode]
    rw [zip_phiState B]
    exact closesLayer_phi_imp hB hnd.2 odd hmid ((ov.count true) / 2 + 1) 0
      (List.zip ov nd.σ) hzip_val h

/-! ## Section 3: Exact Base-6 Digit Lengths & Six-Seed Forward-Orbit Structure -/

/-- Reversing any positive integer `n ≥ 1` in base 6 yields a strictly positive integer. -/
theorem rev6_pos {n : ℕ} (hn : 1 ≤ n) : 0 < rev6 n := by
  have hne0 : n ≠ 0 := by omega
  have hdne : Nat.digits 6 n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hne0
  have hlast : (Nat.digits 6 n).getLast hdne ≠ 0 := Nat.getLast_digit_ne_zero 6 hne0
  unfold rev6
  cases hrev : (Nat.digits 6 n).reverse with
  | nil => exact (hdne (List.reverse_eq_nil_iff.mp hrev)).elim
  | cons d tl =>
    have hdig : Nat.digits 6 n = tl.reverse ++ [d] := by
      have := congrArg List.reverse hrev
      simpa using this
    have hd_ne : d ≠ 0 := by
      intro hd0
      apply hlast
      simp [hdig, hd0]
    simp only [Nat.ofDigits_cons]
    omega

/-- Every positive integer strictly increases under one `revAdd6` step. -/
theorem lt_revAdd6 {n : ℕ} (hn : 1 ≤ n) : n < revAdd6 n := by
  unfold revAdd6
  have := rev6_pos hn
  omega

/-- Every forward iterate `revAdd6^[t] n` of `n ≥ 1` is `≥ 1`. -/
theorem revAdd6_iterate_pos {n : ℕ} (hn : 1 ≤ n) : ∀ t : ℕ, 1 ≤ revAdd6^[t] n
  | 0 => hn
  | t + 1 => by
    rw [Function.iterate_succ_apply']
    have := lt_revAdd6 (revAdd6_iterate_pos hn t)
    omega

/-- **Strict monotonicity of trajectories**: for every `n ≥ 1`, `t ↦ revAdd6^[t] n` is strictly
increasing (`t₁ < t₂ → revAdd6^[t₁] n < revAdd6^[t₂] n`). -/
theorem revAdd6_iterate_strictMono {n : ℕ} (hn : 1 ≤ n) :
    StrictMono (fun t => revAdd6^[t] n) :=
  strictMono_nat_of_lt_succ (fun t => by
    rw [Function.iterate_succ_apply']
    exact lt_revAdd6 (revAdd6_iterate_pos hn t))

/-- Forward invariance of `IsLychrel6`: every forward iterate of a base-6 Lychrel number is itself
a base-6 Lychrel number. -/
theorem IsLychrel6.iterate {n : ℕ} (hn : IsLychrel6 n) (t : ℕ) :
    IsLychrel6 (revAdd6^[t] n) := by
  intro j
  rw [← Function.iterate_add_apply]
  exact hn (j + t)

/-- Exact canonical `Nat.digits 6` length of `xFam m` (`110 + 2 * m`). -/
theorem digits6_xFam_length (m : ℕ) :
    (Nat.digits 6 (xFam m)).length = 110 + 2 * m := by
  unfold xFam formVal
  rw [digits_ofDigits6MSB (xForm0_valid.validMSB6 m), List.length_reverse, xFam_digits_length]

/-- Exact canonical `Nat.digits 6` length of `yFam m` (`108 + 2 * m`). -/
theorem digits6_yFam_length (m : ℕ) :
    (Nat.digits 6 (yFam m)).length = 108 + 2 * m := by
  unfold yFam formVal
  rw [digits_ofDigits6MSB (yForm0_valid.validMSB6 m), List.length_reverse, yFam_digits_length]

/-- Tight power-of-6 bounds on `xFam m`: `6^(109 + 2m) ≤ xFam m < 6^(110 + 2m)`. -/
theorem xFam_pow_bounds (m : ℕ) :
    6 ^ (109 + 2 * m) ≤ xFam m ∧ xFam m < 6 ^ (110 + 2 * m) := by
  have hvalid := xForm0_valid.validMSB6 m
  have hlen := xFam_digits_length m
  refine ⟨?_, ?_⟩
  · have hlow := pow_length_sub_one_le_ofDigits6MSB hvalid
    rw [hlen] at hlow
    simpa [xFam, formVal] using hlow
  · unfold xFam formVal ofDigits6MSB
    have hup := ofDigits6_lt_pow_length (fun d hd => hvalid.2.1 d (List.mem_reverse.mp hd))
    rwa [List.length_reverse, hlen] at hup

/-- Tight power-of-6 bounds on `yFam m`: `6^(107 + 2m) ≤ yFam m < 6^(108 + 2m)`. -/
theorem yFam_pow_bounds (m : ℕ) :
    6 ^ (107 + 2 * m) ≤ yFam m ∧ yFam m < 6 ^ (108 + 2 * m) := by
  have hvalid := yForm0_valid.validMSB6 m
  have hlen := yFam_digits_length m
  refine ⟨?_, ?_⟩
  · have hlow := pow_length_sub_one_le_ofDigits6MSB hvalid
    rw [hlen] at hlow
    simpa [yFam, formVal] using hlow
  · unfold yFam formVal ofDigits6MSB
    have hup := ofDigits6_lt_pow_length (fun d hd => hvalid.2.1 d (List.mem_reverse.mp hd))
    rwa [List.length_reverse, hlen] at hup

/-- Every `xFam m` is strictly positive (`1 ≤ xFam m`). -/
theorem xFam_pos (m : ℕ) : 1 ≤ xFam m :=
  le_trans (Nat.one_le_pow _ _ (by norm_num)) (xFam_pow_bounds m).1

/-- Every `yFam m` is strictly positive (`1 ≤ yFam m`). -/
theorem yFam_pos (m : ℕ) : 1 ≤ yFam m :=
  le_trans (Nat.one_le_pow _ _ (by norm_num)) (yFam_pow_bounds m).1

/-- **Multi-period recurrence (Family 1)**: `revAdd6^[12 * k] (xFam m) = xFam (3 * k + m)`. -/
theorem xFam_iterate_twelve_mul (m : ℕ) :
    ∀ k : ℕ, revAdd6^[12 * k] (xFam m) = xFam (3 * k + m)
  | 0 => by simp
  | k + 1 => by
    have hmul : 12 * (k + 1) = 12 + 12 * k := by omega
    rw [hmul, Function.iterate_add_apply, xFam_iterate_twelve_mul m k, xFam_step12]
    exact congrArg xFam (by omega)

/-- **Multi-period recurrence (Family 2)**: `revAdd6^[12 * k] (yFam m) = yFam (3 * k + m)`. -/
theorem yFam_iterate_twelve_mul (m : ℕ) :
    ∀ k : ℕ, revAdd6^[12 * k] (yFam m) = yFam (3 * k + m)
  | 0 => by simp
  | k + 1 => by
    have hmul : 12 * (k + 1) = 12 + 12 * k := by omega
    rw [hmul, Function.iterate_add_apply, yFam_iterate_twelve_mul m k, yFam_step12]
    exact congrArg yFam (by omega)

/-- Every member `xFam m` lies on the forward orbit of one of the three roots `xFam 0, xFam 1, xFam 2`. -/
theorem xFam_eq_seed_iterate (m : ℕ) :
    xFam m = revAdd6^[12 * (m / 3)] (xFam (m % 3)) := by
  rw [xFam_iterate_twelve_mul]
  exact congrArg xFam (Nat.div_add_mod m 3).symm

/-- Every member `yFam m` lies on the forward orbit of one of the three roots `yFam 0, yFam 1, yFam 2`. -/
theorem yFam_eq_seed_iterate (m : ℕ) :
    yFam m = revAdd6^[12 * (m / 3)] (yFam (m % 3)) := by
  rw [yFam_iterate_twelve_mul]
  exact congrArg yFam (Nat.div_add_mod m 3).symm

/-- Every forward iterate `revAdd6^[t] (xFam m)` is a base-6 Lychrel number. -/
theorem xFam_iterate_lychrel (m t : ℕ) : IsLychrel6 (revAdd6^[t] (xFam m)) :=
  (xFam_lychrel m).iterate t

/-- Every forward iterate `revAdd6^[t] (yFam m)` is a base-6 Lychrel number. -/
theorem yFam_iterate_lychrel (m t : ℕ) : IsLychrel6 (revAdd6^[t] (yFam m)) :=
  (yFam_lychrel m).iterate t

/-- Linear-pass 12-step staircase length checker for small finite base cases `m = 0..5`. -/
def checkDirectLengthsAux : ℕ → ℕ → ℕ → List ℕ → Bool
  | 0, _, _, _ => true
  | rem + 1, idx, baseLen, ds =>
    (ds.length == baseLen + idx / 2) &&
    checkDirectLengthsAux rem (idx + 1) baseLen (revAddMSB6 ds)

private theorem checkDirectLengthsAux_sound :
    ∀ (rem idx baseLen : ℕ) (ds : List ℕ),
      ValidMSB6 ds →
      checkDirectLengthsAux rem idx baseLen ds = true →
      ∀ s < rem, (Nat.digits 6 (revAdd6^[s] (ofDigits6MSB ds))).length = baseLen + (idx + s) / 2
  | 0, _, _, _, _, _, s, hs => by omega
  | rem + 1, idx, baseLen, ds, hds, hchk, s, hs => by
    simp only [checkDirectLengthsAux, Bool.and_eq_true, beq_iff_eq] at hchk
    cases s with
    | zero =>
      rw [Function.iterate_zero_apply, digits_ofDigits6MSB hds, List.length_reverse, hchk.1]
      simp
    | succ s' =>
      rw [Function.iterate_succ_apply, ← ofDigits6MSB_revAddMSB6 hds]
      have ih := checkDirectLengthsAux_sound rem (idx + 1) baseLen (revAddMSB6 ds)
        (revAddMSB6_valid hds) hchk.2 s' (by omega)
      rw [ih]
      congr 1
      omega

private theorem xForm0_allValid12 : allValidBefore xForm0 12 = true := by
  decide

private theorem yForm0_allValid12 : allValidBefore yForm0 12 = true := by
  decide

/-- Symbolic evaluation of `revAdd6^[s] (xFam m)` for `m ≥ 6` and `s < 12`. -/
theorem xFam_iterate_lt12_eq_formVal {m s : ℕ} (hm : 6 ≤ m) (hs : s < 12) :
    revAdd6^[s] (xFam m) = formVal (xForms13.getD s xForm0) (m - s / 2) := by
  have hs_le : s ≤ 12 := Nat.le_of_lt hs
  have hvalid : allValidBefore xForm0 s = true := allValidBefore_of_le hs_le xForm0_allValid12
  have hst := stepFormN_xForm0_eq hs_le
  have hov : (stepFormN xForm0 s).2 ≤ m := by rw [hst.2]; omega
  unfold xFam
  rw [stepFormN_sound s m hvalid hov, hst.1, hst.2]

/-- Symbolic evaluation of `revAdd6^[s] (yFam m)` for `m ≥ 6` and `s < 12`. -/
theorem yFam_iterate_lt12_eq_formVal {m s : ℕ} (hm : 6 ≤ m) (hs : s < 12) :
    revAdd6^[s] (yFam m) = formVal (yForms13.getD s yForm0) (m - s / 2) := by
  have hs_le : s ≤ 12 := Nat.le_of_lt hs
  have hvalid : allValidBefore yForm0 s = true := allValidBefore_of_le hs_le yForm0_allValid12
  have hst := stepFormN_yForm0_eq hs_le
  have hov : (stepFormN yForm0 s).2 ≤ m := by rw [hst.2]; omega
  unfold yFam
  rw [stepFormN_sound s m hvalid hov, hst.1, hst.2]

private theorem xForms13_valid {s : ℕ} (hs : s < 12) : ValidForm (xForms13.getD s xForm0) := by
  have h := validForm_stepFormN_of_lt hs xForm0_allValid12
  rwa [(stepFormN_xForm0_eq (Nat.le_of_lt hs)).1] at h

private theorem yForms13_valid {s : ℕ} (hs : s < 12) : ValidForm (yForms13.getD s yForm0) := by
  have h := validForm_stepFormN_of_lt hs yForm0_allValid12
  rwa [(stepFormN_yForm0_eq (Nat.le_of_lt hs)).1] at h

private theorem digits6_iterate_xFam_lt12 (m : ℕ) {s : ℕ} (hs : s < 12) :
    (Nat.digits 6 (revAdd6^[s] (xFam m))).length = 110 + 2 * m + s / 2 := by
  match m with
  | 0 => simpa [xFam, formVal] using checkDirectLengthsAux_sound 12 0 110 _ (xForm0_valid.validMSB6 0) (by decide) s hs
  | 1 => simpa [xFam, formVal] using checkDirectLengthsAux_sound 12 0 112 _ (xForm0_valid.validMSB6 1) (by decide) s hs
  | 2 => simpa [xFam, formVal] using checkDirectLengthsAux_sound 12 0 114 _ (xForm0_valid.validMSB6 2) (by decide) s hs
  | 3 => simpa [xFam, formVal] using checkDirectLengthsAux_sound 12 0 116 _ (xForm0_valid.validMSB6 3) (by decide) s hs
  | 4 => simpa [xFam, formVal] using checkDirectLengthsAux_sound 12 0 118 _ (xForm0_valid.validMSB6 4) (by decide) s hs
  | 5 => simpa [xFam, formVal] using checkDirectLengthsAux_sound 12 0 120 _ (xForm0_valid.validMSB6 5) (by decide) s hs
  | m' + 6 =>
    have hm : 6 ≤ m' + 6 := by omega
    rw [xFam_iterate_lt12_eq_formVal hm hs]
    unfold formVal
    rw [digits_ofDigits6MSB ((xForms13_valid hs).validMSB6 _), List.length_reverse, evalForm_length]
    have hblk : (xForms13.getD s xForm0).A.length + (xForms13.getD s xForm0).M.length +
        (xForms13.getD s xForm0).Z.length = 110 + 2 * (s / 2) + s / 2 := by
      interval_cases s <;> decide
    rw [hblk]
    omega

private theorem digits6_iterate_yFam_lt12 (m : ℕ) {s : ℕ} (hs : s < 12) :
    (Nat.digits 6 (revAdd6^[s] (yFam m))).length = 108 + 2 * m + s / 2 := by
  match m with
  | 0 => simpa [yFam, formVal] using checkDirectLengthsAux_sound 12 0 108 _ (yForm0_valid.validMSB6 0) (by decide) s hs
  | 1 => simpa [yFam, formVal] using checkDirectLengthsAux_sound 12 0 110 _ (yForm0_valid.validMSB6 1) (by decide) s hs
  | 2 => simpa [yFam, formVal] using checkDirectLengthsAux_sound 12 0 112 _ (yForm0_valid.validMSB6 2) (by decide) s hs
  | 3 => simpa [yFam, formVal] using checkDirectLengthsAux_sound 12 0 114 _ (yForm0_valid.validMSB6 3) (by decide) s hs
  | 4 => simpa [yFam, formVal] using checkDirectLengthsAux_sound 12 0 116 _ (yForm0_valid.validMSB6 4) (by decide) s hs
  | 5 => simpa [yFam, formVal] using checkDirectLengthsAux_sound 12 0 118 _ (yForm0_valid.validMSB6 5) (by decide) s hs
  | m' + 6 =>
    have hm : 6 ≤ m' + 6 := by omega
    rw [yFam_iterate_lt12_eq_formVal hm hs]
    unfold formVal
    rw [digits_ofDigits6MSB ((yForms13_valid hs).validMSB6 _), List.length_reverse, evalForm_length]
    have hblk : (yForms13.getD s yForm0).A.length + (yForms13.getD s yForm0).M.length +
        (yForms13.getD s yForm0).Z.length = 108 + 2 * (s / 2) + s / 2 := by
      interval_cases s <;> decide
    rw [hblk]
    omega

/-- **Exact staircase digit-length formula (Family 1)**: for ALL `m, t : ℕ`,
`(Nat.digits 6 (revAdd6^[t] (xFam m))).length = 110 + 2 * m + t / 2`. -/
theorem digits6_iterate_xFam_length (m t : ℕ) :
    (Nat.digits 6 (revAdd6^[t] (xFam m))).length = 110 + 2 * m + t / 2 := by
  have ht : t = t % 12 + 12 * (t / 12) := by
    have := Nat.div_add_mod t 12
    omega
  conv_lhs => rw [ht]
  rw [Function.iterate_add_apply, xFam_iterate_twelve_mul,
    digits6_iterate_xFam_lt12 _ (Nat.mod_lt t (by norm_num))]
  omega

/-- **Exact staircase digit-length formula (Family 2)**: for ALL `m, t : ℕ`,
`(Nat.digits 6 (revAdd6^[t] (yFam m))).length = 108 + 2 * m + t / 2`. -/
theorem digits6_iterate_yFam_length (m t : ℕ) :
    (Nat.digits 6 (revAdd6^[t] (yFam m))).length = 108 + 2 * m + t / 2 := by
  have ht : t = t % 12 + 12 * (t / 12) := by
    have := Nat.div_add_mod t 12
    omega
  conv_lhs => rw [ht]
  rw [Function.iterate_add_apply, yFam_iterate_twelve_mul,
    digits6_iterate_yFam_lt12 _ (Nat.mod_lt t (by norm_num))]
  omega

/-- Tight power-of-6 bounds on every iterate `revAdd6^[t] (xFam m)`. -/
theorem iterate_xFam_pow_bounds (m t : ℕ) :
    6 ^ (109 + 2 * m + t / 2) ≤ revAdd6^[t] (xFam m) ∧
    revAdd6^[t] (xFam m) < 6 ^ (110 + 2 * m + t / 2) := by
  have hvalid : ValidMSB6 (revAddMSB6^[t] (evalForm xForm0 m)) :=
    revAddMSB6_iterate_valid (xForm0_valid.validMSB6 m) t
  have hval : revAdd6^[t] (xFam m) = ofDigits6MSB (revAddMSB6^[t] (evalForm xForm0 m)) :=
    revAdd6_iterate_ofDigits6MSB (xForm0_valid.validMSB6 m) t
  have hlen : (revAddMSB6^[t] (evalForm xForm0 m)).length = 110 + 2 * m + t / 2 := by
    have hd := digits6_iterate_xFam_length m t
    rw [hval, digits_ofDigits6MSB hvalid, List.length_reverse] at hd
    exact hd
  refine ⟨?_, ?_⟩
  · have hlow := pow_length_sub_one_le_ofDigits6MSB hvalid
    have hexp : (revAddMSB6^[t] (evalForm xForm0 m)).length - 1 = 109 + 2 * m + t / 2 := by omega
    rw [hexp, ← hval] at hlow
    exact hlow
  · rw [hval]
    unfold ofDigits6MSB
    have hup := ofDigits6_lt_pow_length (fun d hd => hvalid.2.1 d (List.mem_reverse.mp hd))
    rwa [List.length_reverse, hlen] at hup

/-- Tight power-of-6 bounds on every iterate `revAdd6^[t] (yFam m)`. -/
theorem iterate_yFam_pow_bounds (m t : ℕ) :
    6 ^ (107 + 2 * m + t / 2) ≤ revAdd6^[t] (yFam m) ∧
    revAdd6^[t] (yFam m) < 6 ^ (108 + 2 * m + t / 2) := by
  have hvalid : ValidMSB6 (revAddMSB6^[t] (evalForm yForm0 m)) :=
    revAddMSB6_iterate_valid (yForm0_valid.validMSB6 m) t
  have hval : revAdd6^[t] (yFam m) = ofDigits6MSB (revAddMSB6^[t] (evalForm yForm0 m)) :=
    revAdd6_iterate_ofDigits6MSB (yForm0_valid.validMSB6 m) t
  have hlen : (revAddMSB6^[t] (evalForm yForm0 m)).length = 108 + 2 * m + t / 2 := by
    have hd := digits6_iterate_yFam_length m t
    rw [hval, digits_ofDigits6MSB hvalid, List.length_reverse] at hd
    exact hd
  refine ⟨?_, ?_⟩
  · have hlow := pow_length_sub_one_le_ofDigits6MSB hvalid
    have hexp : (revAddMSB6^[t] (evalForm yForm0 m)).length - 1 = 107 + 2 * m + t / 2 := by omega
    rw [hexp, ← hval] at hlow
    exact hlow
  · rw [hval]
    unfold ofDigits6MSB
    have hup := ofDigits6_lt_pow_length (fun d hd => hvalid.2.1 d (List.mem_reverse.mp hd))
    rwa [List.length_reverse, hlen] at hup

private theorem evalForm_getElem?_prefix (F : Form) (k i : ℕ) (hi : i < F.A.length) :
    (evalForm F k)[i]? = F.A[i]? := by
  unfold evalForm
  simp only [List.append_assoc]
  exact List.getElem?_append_left hi

private theorem evalForm_getElem?_mid (F : Form) (k j : ℕ) (hj : j < F.M.length) :
    (evalForm F k)[F.A.length + k + j]? = F.M[j]? := by
  unfold evalForm
  have hassoc : F.A ++ List.replicate k F.h ++ F.M ++ List.replicate k F.l ++ F.Z =
      (F.A ++ List.replicate k F.h) ++ (F.M ++ (List.replicate k F.l ++ F.Z)) := by
    simp [List.append_assoc]
  rw [hassoc]
  have hpre : (F.A ++ List.replicate k F.h).length = F.A.length + k := by simp
  rw [List.getElem?_append_right (by omega), hpre, Nat.add_sub_cancel_left,
    List.getElem?_append_left hj]

private theorem xFam_ne_iterate_lt12 {m₁ m₂ u : ℕ} (hm₂ : 6 ≤ m₂)
    (hu0 : 1 ≤ u) (hu12 : u < 12) :
    xFam m₁ ≠ revAdd6^[u] (xFam m₂) := by
  intro heq
  have hlen := congrArg (fun n => (Nat.digits 6 n).length) heq
  rw [digits6_xFam_length, digits6_iterate_xFam_length] at hlen
  rw [xFam_iterate_lt12_eq_formVal hm₂ hu12] at heq
  have hlist : evalForm xForm0 m₁ = evalForm (xForms13.getD u xForm0) (m₂ - u / 2) :=
    ofDigits6MSB_inj (xForm0_valid.validMSB6 m₁)
      ((xForms13_valid hu12).validMSB6 (m₂ - u / 2)) heq
  interval_cases u
  · have h0 := congrArg (fun l => l[0]?) hlist
    rw [evalForm_getElem?_prefix xForm0 _ 0 (by decide),
      evalForm_getElem?_prefix _ _ 0 (by decide)] at h0
    revert h0; decide
  · omega
  · omega
  · obtain ⟨k, rfl⟩ : ∃ k, m₂ = k + 2 := ⟨m₂ - 2, by omega⟩
    have hm₁_eq : m₁ = k + 3 := by omega
    subst hm₁_eq
    have hsub : k + 2 - 4 / 2 = k := by omega
    rw [hsub] at hlist
    have hidx := congrArg (fun l => l[k + 9]?) hlist
    have hi1 : k + 9 = xForm0.A.length + (k + 3) + 0 := by
      have : xForm0.A.length = 6 := rfl
      omega
    have hi2 : k + 9 = (xForms13.getD 4 xForm0).A.length + k + 1 := by
      have : (xForms13.getD 4 xForm0).A.length = 8 := by decide
      omega
    have h1 : (evalForm xForm0 (k + 3))[k + 9]? = xForm0.M[0]? := by
      rw [hi1]; exact evalForm_getElem?_mid xForm0 (k + 3) 0 (by decide)
    have h2 : (evalForm (xForms13.getD 4 xForm0) k)[k + 9]? = (xForms13.getD 4 xForm0).M[1]? := by
      rw [hi2]; exact evalForm_getElem?_mid (xForms13.getD 4 xForm0) k 1 (by decide)
    rw [h1, h2] at hidx
    revert hidx; decide
  · have h0 := congrArg (fun l => l[0]?) hlist
    rw [evalForm_getElem?_prefix xForm0 _ 0 (by decide),
      evalForm_getElem?_prefix _ _ 0 (by decide)] at h0
    revert h0; decide
  · omega
  · omega
  · obtain ⟨k, rfl⟩ : ∃ k, m₂ = k + 4 := ⟨m₂ - 4, by omega⟩
    have hm₁_eq : m₁ = k + 6 := by omega
    subst hm₁_eq
    have hsub : k + 4 - 8 / 2 = k := by omega
    rw [hsub] at hlist
    have hidx := congrArg (fun l => l[k + 12]?) hlist
    have hi1 : k + 12 = xForm0.A.length + (k + 6) + 0 := by
      have : xForm0.A.length = 6 := rfl
      omega
    have hi2 : k + 12 = (xForms13.getD 8 xForm0).A.length + k + 2 := by
      have : (xForms13.getD 8 xForm0).A.length = 10 := by decide
      omega
    have h1 : (evalForm xForm0 (k + 6))[k + 12]? = xForm0.M[0]? := by
      rw [hi1]; exact evalForm_getElem?_mid xForm0 (k + 6) 0 (by decide)
    have h2 : (evalForm (xForms13.getD 8 xForm0) k)[k + 12]? = (xForms13.getD 8 xForm0).M[2]? := by
      rw [hi2]; exact evalForm_getElem?_mid (xForms13.getD 8 xForm0) k 2 (by decide)
    rw [h1, h2] at hidx
    revert hidx; decide
  · have h0 := congrArg (fun l => l[0]?) hlist
    rw [evalForm_getElem?_prefix xForm0 _ 0 (by decide),
      evalForm_getElem?_prefix _ _ 0 (by decide)] at h0
    revert h0; decide
  · omega
  · omega

private theorem yFam_ne_iterate_lt12 {m₁ m₂ u : ℕ} (hm₂ : 6 ≤ m₂)
    (hu0 : 1 ≤ u) (hu12 : u < 12) :
    yFam m₁ ≠ revAdd6^[u] (yFam m₂) := by
  intro heq
  have hlen := congrArg (fun n => (Nat.digits 6 n).length) heq
  rw [digits6_yFam_length, digits6_iterate_yFam_length] at hlen
  rw [yFam_iterate_lt12_eq_formVal hm₂ hu12] at heq
  have hlist : evalForm yForm0 m₁ = evalForm (yForms13.getD u yForm0) (m₂ - u / 2) :=
    ofDigits6MSB_inj (yForm0_valid.validMSB6 m₁)
      ((yForms13_valid hu12).validMSB6 (m₂ - u / 2)) heq
  interval_cases u
  · have h0 := congrArg (fun l => l[0]?) hlist
    rw [evalForm_getElem?_prefix yForm0 _ 0 (by decide),
      evalForm_getElem?_prefix _ _ 0 (by decide)] at h0
    revert h0; decide
  · omega
  · omega
  · obtain ⟨k, rfl⟩ : ∃ k, m₂ = k + 2 := ⟨m₂ - 2, by omega⟩
    have hm₁_eq : m₁ = k + 3 := by omega
    subst hm₁_eq
    have hsub : k + 2 - 4 / 2 = k := by omega
    rw [hsub] at hlist
    have hidx := congrArg (fun l => l[k + 8]?) hlist
    have hi1 : k + 8 = yForm0.A.length + (k + 3) + 0 := by
      have : yForm0.A.length = 5 := rfl
      omega
    have hi2 : k + 8 = (yForms13.getD 4 yForm0).A.length + k + 1 := by
      have : (yForms13.getD 4 yForm0).A.length = 7 := by decide
      omega
    have h1 : (evalForm yForm0 (k + 3))[k + 8]? = yForm0.M[0]? := by
      rw [hi1]; exact evalForm_getElem?_mid yForm0 (k + 3) 0 (by decide)
    have h2 : (evalForm (yForms13.getD 4 yForm0) k)[k + 8]? = (yForms13.getD 4 yForm0).M[1]? := by
      rw [hi2]; exact evalForm_getElem?_mid (yForms13.getD 4 yForm0) k 1 (by decide)
    rw [h1, h2] at hidx
    revert hidx; decide
  · have h0 := congrArg (fun l => l[0]?) hlist
    rw [evalForm_getElem?_prefix yForm0 _ 0 (by decide),
      evalForm_getElem?_prefix _ _ 0 (by decide)] at h0
    revert h0; decide
  · omega
  · omega
  · obtain ⟨k, rfl⟩ : ∃ k, m₂ = k + 4 := ⟨m₂ - 4, by omega⟩
    have hm₁_eq : m₁ = k + 6 := by omega
    subst hm₁_eq
    have hsub : k + 4 - 8 / 2 = k := by omega
    rw [hsub] at hlist
    have hidx := congrArg (fun l => l[k + 11]?) hlist
    have hi1 : k + 11 = yForm0.A.length + (k + 6) + 0 := by
      have : yForm0.A.length = 5 := rfl
      omega
    have hi2 : k + 11 = (yForms13.getD 8 yForm0).A.length + k + 2 := by
      have : (yForms13.getD 8 yForm0).A.length = 9 := by decide
      omega
    have h1 : (evalForm yForm0 (k + 6))[k + 11]? = yForm0.M[0]? := by
      rw [hi1]; exact evalForm_getElem?_mid yForm0 (k + 6) 0 (by decide)
    have h2 : (evalForm (yForms13.getD 8 yForm0) k)[k + 11]? = (yForms13.getD 8 yForm0).M[2]? := by
      rw [hi2]; exact evalForm_getElem?_mid (yForms13.getD 8 yForm0) k 2 (by decide)
    rw [h1, h2] at hidx
    revert hidx; decide
  · have h0 := congrArg (fun l => l[0]?) hlist
    rw [evalForm_getElem?_prefix yForm0 _ 0 (by decide),
      evalForm_getElem?_prefix _ _ 0 (by decide)] at h0
    revert h0; decide
  · omega
  · omega

private theorem xFam_ne_iterate_yFam_lt12 {m₁ m₂ u : ℕ} (hm₂ : 6 ≤ m₂) (hu12 : u < 12) :
    xFam m₁ ≠ revAdd6^[u] (yFam m₂) := by
  intro heq
  rw [yFam_iterate_lt12_eq_formVal hm₂ hu12] at heq
  have hlist : evalForm xForm0 m₁ = evalForm (yForms13.getD u yForm0) (m₂ - u / 2) :=
    ofDigits6MSB_inj (xForm0_valid.validMSB6 m₁)
      ((yForms13_valid hu12).validMSB6 (m₂ - u / 2)) heq
  have h3 := congrArg (fun l => l[3]?) hlist
  interval_cases u <;>
    (rw [evalForm_getElem?_prefix xForm0 _ 3 (by decide),
         evalForm_getElem?_prefix _ _ 3 (by decide)] at h3;
     revert h3; decide)

/-- **Injectivity / Pairwise Disjointness of Family 1's Three Seed Trajectories**:
for `r₁, r₂ < 3` and `t₁, t₂ : ℕ`, `revAdd6^[t₁] (xFam r₁) = revAdd6^[t₂] (xFam r₂)` implies
`r₁ = r₂` and `t₁ = t₂`. -/
theorem xSeed_orbits_inj {r₁ r₂ t₁ t₂ : ℕ} (hr₁ : r₁ < 3) (hr₂ : r₂ < 3)
    (heq : revAdd6^[t₁] (xFam r₁) = revAdd6^[t₂] (xFam r₂)) :
    r₁ = r₂ ∧ t₁ = t₂ := by
  set s₁ := t₁ % 12
  set q₁ := t₁ / 12
  set shift := 72 + (12 - s₁)
  have hshift := congrArg (revAdd6^[shift]) heq
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at hshift
  have hL : shift + t₁ = 12 * (q₁ + 7) := by
    have := Nat.div_add_mod t₁ 12
    have : s₁ < 12 := Nat.mod_lt t₁ (by norm_num)
    omega
  set T₂ := shift + t₂
  set u := T₂ % 12
  set Q₂ := T₂ / 12
  have hR : T₂ = u + 12 * Q₂ := by
    have := Nat.div_add_mod T₂ 12
    omega
  rw [hL, hR, xFam_iterate_twelve_mul, Function.iterate_add_apply, xFam_iterate_twelve_mul] at hshift
  have hm₂ : 6 ≤ 3 * Q₂ + r₂ := by
    have : 72 ≤ T₂ := by omega
    omega
  have hu12 : u < 12 := Nat.mod_lt T₂ (by norm_num)
  by_cases hu0 : u = 0
  · rw [hu0, Function.iterate_zero_apply] at hshift
    have hinj := xFam_strictMono.injective hshift
    have hr_eq : r₁ = r₂ := by omega
    subst hr_eq
    exact ⟨rfl, (revAdd6_iterate_strictMono (xFam_pos r₁)).injective heq⟩
  · exact (xFam_ne_iterate_lt12 hm₂ (by omega) hu12 hshift).elim

/-- **Injectivity / Pairwise Disjointness of Family 2's Three Seed Trajectories**:
for `r₁, r₂ < 3` and `t₁, t₂ : ℕ`, `revAdd6^[t₁] (yFam r₁) = revAdd6^[t₂] (yFam r₂)` implies
`r₁ = r₂` and `t₁ = t₂`. -/
theorem ySeed_orbits_inj {r₁ r₂ t₁ t₂ : ℕ} (hr₁ : r₁ < 3) (hr₂ : r₂ < 3)
    (heq : revAdd6^[t₁] (yFam r₁) = revAdd6^[t₂] (yFam r₂)) :
    r₁ = r₂ ∧ t₁ = t₂ := by
  set s₁ := t₁ % 12
  set q₁ := t₁ / 12
  set shift := 72 + (12 - s₁)
  have hshift := congrArg (revAdd6^[shift]) heq
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at hshift
  have hL : shift + t₁ = 12 * (q₁ + 7) := by
    have := Nat.div_add_mod t₁ 12
    have : s₁ < 12 := Nat.mod_lt t₁ (by norm_num)
    omega
  set T₂ := shift + t₂
  set u := T₂ % 12
  set Q₂ := T₂ / 12
  have hR : T₂ = u + 12 * Q₂ := by
    have := Nat.div_add_mod T₂ 12
    omega
  rw [hL, hR, yFam_iterate_twelve_mul, Function.iterate_add_apply, yFam_iterate_twelve_mul] at hshift
  have hm₂ : 6 ≤ 3 * Q₂ + r₂ := by
    have : 72 ≤ T₂ := by omega
    omega
  have hu12 : u < 12 := Nat.mod_lt T₂ (by norm_num)
  by_cases hu0 : u = 0
  · rw [hu0, Function.iterate_zero_apply] at hshift
    have hinj := yFam_strictMono.injective hshift
    have hr_eq : r₁ = r₂ := by omega
    subst hr_eq
    exact ⟨rfl, (revAdd6_iterate_strictMono (yFam_pos r₁)).injective heq⟩
  · exact (yFam_ne_iterate_lt12 hm₂ (by omega) hu12 hshift).elim

/-- **Complete Cross-Family Orbit Disjointness**: no forward iterate of ANY `xFam m₁` ever
intersects any forward iterate of ANY `yFam m₂`. -/
theorem xFam_orbit_ne_yFam_orbit (m₁ m₂ t₁ t₂ : ℕ) :
    revAdd6^[t₁] (xFam m₁) ≠ revAdd6^[t₂] (yFam m₂) := by
  intro heq
  set s₁ := t₁ % 12
  set q₁ := t₁ / 12
  set shift := 72 + (12 - s₁)
  have hshift := congrArg (revAdd6^[shift]) heq
  rw [← Function.iterate_add_apply, ← Function.iterate_add_apply] at hshift
  have hL : shift + t₁ = 12 * (q₁ + 7) := by
    have := Nat.div_add_mod t₁ 12
    have : s₁ < 12 := Nat.mod_lt t₁ (by norm_num)
    omega
  set T₂ := shift + t₂
  set u := T₂ % 12
  set Q₂ := T₂ / 12
  have hR : T₂ = u + 12 * Q₂ := by
    have := Nat.div_add_mod T₂ 12
    omega
  rw [hL, hR, xFam_iterate_twelve_mul, Function.iterate_add_apply, yFam_iterate_twelve_mul] at hshift
  have hm₂ : 6 ≤ 3 * Q₂ + m₂ := by
    have : 72 ≤ T₂ := by omega
    omega
  exact xFam_ne_iterate_yFam_lt12 hm₂ (Nat.mod_lt T₂ (by norm_num)) hshift

/-- Pairwise set disjointness of `{revAdd6^[t] (xFam r₁) | t}` and `{revAdd6^[t] (xFam r₂) | t}`
for distinct `r₁, r₂ < 3`. -/
theorem xSeed_trajectories_disjoint {r₁ r₂ : ℕ} (hr₁ : r₁ < 3) (hr₂ : r₂ < 3) (hne : r₁ ≠ r₂) :
    Disjoint (Set.range (fun t => revAdd6^[t] (xFam r₁)))
      (Set.range (fun t => revAdd6^[t] (xFam r₂))) := by
  rw [Set.disjoint_left]
  rintro _ ⟨t₁, rfl⟩ ⟨t₂, heq⟩
  exact hne (xSeed_orbits_inj hr₁ hr₂ heq.symm).1

/-- Pairwise set disjointness of `{revAdd6^[t] (yFam r₁) | t}` and `{revAdd6^[t] (yFam r₂) | t}`
for distinct `r₁, r₂ < 3`. -/
theorem ySeed_trajectories_disjoint {r₁ r₂ : ℕ} (hr₁ : r₁ < 3) (hr₂ : r₂ < 3) (hne : r₁ ≠ r₂) :
    Disjoint (Set.range (fun t => revAdd6^[t] (yFam r₁)))
      (Set.range (fun t => revAdd6^[t] (yFam r₂))) := by
  rw [Set.disjoint_left]
  rintro _ ⟨t₁, rfl⟩ ⟨t₂, heq⟩
  exact hne (ySeed_orbits_inj hr₁ hr₂ heq.symm).1

/-- Complete set disjointness of `{revAdd6^[t] (xFam m₁) | t}` and `{revAdd6^[t] (yFam m₂) | t}`. -/
theorem xFam_yFam_trajectories_disjoint (m₁ m₂ : ℕ) :
    Disjoint (Set.range (fun t => revAdd6^[t] (xFam m₁)))
      (Set.range (fun t => revAdd6^[t] (yFam m₂))) := by
  rw [Set.disjoint_left]
  rintro _ ⟨t₁, rfl⟩ ⟨t₂, heq⟩
  exact xFam_orbit_ne_yFam_orbit m₁ m₂ t₁ t₂ heq.symm

/-- Enumeration of the six root seeds `x(0), x(1), x(2), y(0), y(1), y(2)`. -/
def sixSeed : Fin 6 → ℕ
  | ⟨0, _⟩ => xFam 0
  | ⟨1, _⟩ => xFam 1
  | ⟨2, _⟩ => xFam 2
  | ⟨3, _⟩ => yFam 0
  | ⟨4, _⟩ => yFam 1
  | ⟨5, _⟩ => yFam 2

/-- Initial base-6 digit lengths of the six root seeds (`110, 112, 114, 108, 110, 112`). -/
def sixSeedBaseLen : Fin 6 → ℕ
  | ⟨0, _⟩ => 110
  | ⟨1, _⟩ => 112
  | ⟨2, _⟩ => 114
  | ⟨3, _⟩ => 108
  | ⟨4, _⟩ => 110
  | ⟨5, _⟩ => 112

/-- Unified six-seed forward-orbit parameterization `(s, t) ↦ revAdd6^[t] (sixSeed s)`. -/
def sixSeedMap (p : Fin 6 × ℕ) : ℕ :=
  revAdd6^[p.2] (sixSeed p.1)

/-- Every `sixSeedMap (s, t)` is positive and a base-6 Lychrel number. -/
theorem sixSeedMap_pos_and_lychrel (p : Fin 6 × ℕ) :
    1 ≤ sixSeedMap p ∧ IsLychrel6 (sixSeedMap p) := by
  rcases p with ⟨s, t⟩
  fin_cases s
  · exact ⟨revAdd6_iterate_pos (xFam_pos 0) t, xFam_iterate_lychrel 0 t⟩
  · exact ⟨revAdd6_iterate_pos (xFam_pos 1) t, xFam_iterate_lychrel 1 t⟩
  · exact ⟨revAdd6_iterate_pos (xFam_pos 2) t, xFam_iterate_lychrel 2 t⟩
  · exact ⟨revAdd6_iterate_pos (yFam_pos 0) t, yFam_iterate_lychrel 0 t⟩
  · exact ⟨revAdd6_iterate_pos (yFam_pos 1) t, yFam_iterate_lychrel 1 t⟩
  · exact ⟨revAdd6_iterate_pos (yFam_pos 2) t, yFam_iterate_lychrel 2 t⟩

/-- Exact base-6 digit length and power-of-6 upper bound for `sixSeedMap (s, t)`. -/
theorem sixSeedMap_length_and_lt_pow (p : Fin 6 × ℕ) :
    (Nat.digits 6 (sixSeedMap p)).length = sixSeedBaseLen p.1 + p.2 / 2 ∧
    sixSeedMap p < 6 ^ (sixSeedBaseLen p.1 + p.2 / 2) := by
  rcases p with ⟨s, t⟩
  fin_cases s
  · exact ⟨digits6_iterate_xFam_length 0 t, (iterate_xFam_pow_bounds 0 t).2⟩
  · exact ⟨digits6_iterate_xFam_length 1 t, (iterate_xFam_pow_bounds 1 t).2⟩
  · exact ⟨digits6_iterate_xFam_length 2 t, (iterate_xFam_pow_bounds 2 t).2⟩
  · exact ⟨digits6_iterate_yFam_length 0 t, (iterate_yFam_pow_bounds 0 t).2⟩
  · exact ⟨digits6_iterate_yFam_length 1 t, (iterate_yFam_pow_bounds 1 t).2⟩
  · exact ⟨digits6_iterate_yFam_length 2 t, (iterate_yFam_pow_bounds 2 t).2⟩

/-- **Global Six-Trajectory Bijection / Injectivity Theorem**:
`sixSeedMap : Fin 6 × ℕ → ℕ` is injective — all six infinite forward trajectories
`{revAdd6^[t] (xFam r)}` and `{revAdd6^[t] (yFam r)}` (`r ∈ {0, 1, 2}`) are strictly increasing
and mutually disjoint. -/
theorem sixSeedMap_injective : Function.Injective sixSeedMap := by
  rintro ⟨s₁, t₁⟩ ⟨s₂, t₂⟩ heq
  fin_cases s₁ <;> fin_cases s₂
  · exact Prod.ext rfl (xSeed_orbits_inj (by norm_num) (by norm_num) heq).2
  · exfalso; exact (by norm_num : (0 : ℕ) ≠ 1) (xSeed_orbits_inj (by norm_num) (by norm_num) heq).1
  · exfalso; exact (by norm_num : (0 : ℕ) ≠ 2) (xSeed_orbits_inj (by norm_num) (by norm_num) heq).1
  · exact (xFam_orbit_ne_yFam_orbit 0 0 t₁ t₂ heq).elim
  · exact (xFam_orbit_ne_yFam_orbit 0 1 t₁ t₂ heq).elim
  · exact (xFam_orbit_ne_yFam_orbit 0 2 t₁ t₂ heq).elim
  · exfalso; exact (by norm_num : (1 : ℕ) ≠ 0) (xSeed_orbits_inj (by norm_num) (by norm_num) heq).1
  · exact Prod.ext rfl (xSeed_orbits_inj (by norm_num) (by norm_num) heq).2
  · exfalso; exact (by norm_num : (1 : ℕ) ≠ 2) (xSeed_orbits_inj (by norm_num) (by norm_num) heq).1
  · exact (xFam_orbit_ne_yFam_orbit 1 0 t₁ t₂ heq).elim
  · exact (xFam_orbit_ne_yFam_orbit 1 1 t₁ t₂ heq).elim
  · exact (xFam_orbit_ne_yFam_orbit 1 2 t₁ t₂ heq).elim
  · exfalso; exact (by norm_num : (2 : ℕ) ≠ 0) (xSeed_orbits_inj (by norm_num) (by norm_num) heq).1
  · exfalso; exact (by norm_num : (2 : ℕ) ≠ 1) (xSeed_orbits_inj (by norm_num) (by norm_num) heq).1
  · exact Prod.ext rfl (xSeed_orbits_inj (by norm_num) (by norm_num) heq).2
  · exact (xFam_orbit_ne_yFam_orbit 2 0 t₁ t₂ heq).elim
  · exact (xFam_orbit_ne_yFam_orbit 2 1 t₁ t₂ heq).elim
  · exact (xFam_orbit_ne_yFam_orbit 2 2 t₁ t₂ heq).elim
  · exact (xFam_orbit_ne_yFam_orbit 0 0 t₂ t₁ heq.symm).elim
  · exact (xFam_orbit_ne_yFam_orbit 1 0 t₂ t₁ heq.symm).elim
  · exact (xFam_orbit_ne_yFam_orbit 2 0 t₂ t₁ heq.symm).elim
  · exact Prod.ext rfl (ySeed_orbits_inj (by norm_num) (by norm_num) heq).2
  · exfalso; exact (by norm_num : (0 : ℕ) ≠ 1) (ySeed_orbits_inj (by norm_num) (by norm_num) heq).1
  · exfalso; exact (by norm_num : (0 : ℕ) ≠ 2) (ySeed_orbits_inj (by norm_num) (by norm_num) heq).1
  · exact (xFam_orbit_ne_yFam_orbit 0 1 t₂ t₁ heq.symm).elim
  · exact (xFam_orbit_ne_yFam_orbit 1 1 t₂ t₁ heq.symm).elim
  · exact (xFam_orbit_ne_yFam_orbit 2 1 t₂ t₁ heq.symm).elim
  · exfalso; exact (by norm_num : (1 : ℕ) ≠ 0) (ySeed_orbits_inj (by norm_num) (by norm_num) heq).1
  · exact Prod.ext rfl (ySeed_orbits_inj (by norm_num) (by norm_num) heq).2
  · exfalso; exact (by norm_num : (1 : ℕ) ≠ 2) (ySeed_orbits_inj (by norm_num) (by norm_num) heq).1
  · exact (xFam_orbit_ne_yFam_orbit 0 2 t₂ t₁ heq.symm).elim
  · exact (xFam_orbit_ne_yFam_orbit 1 2 t₂ t₁ heq.symm).elim
  · exact (xFam_orbit_ne_yFam_orbit 2 2 t₂ t₁ heq.symm).elim
  · exfalso; exact (by norm_num : (2 : ℕ) ≠ 0) (ySeed_orbits_inj (by norm_num) (by norm_num) heq).1
  · exfalso; exact (by norm_num : (2 : ℕ) ≠ 1) (ySeed_orbits_inj (by norm_num) (by norm_num) heq).1
  · exact Prod.ext rfl (ySeed_orbits_inj (by norm_num) (by norm_num) heq).2

/-! ## Section 4: Explicit Quantitative Counting Lower Bounds for Base-6 Lychrel Numbers -/

/-- Exact step count `t` along a seed of initial digit length `L₀` whose iterates have at most `D`
base-6 digits (`< 6 ^ D`). -/
def seedCount (D L₀ : ℕ) : ℕ :=
  if L₀ ≤ D then 2 * (D + 1 - L₀) else 0

/-- Index set of `(seed, step)` pairs whose iterates have at most `D` base-6 digits (`< 6 ^ D`). -/
def orbitPairsFinset (D : ℕ) : Finset (Fin 6 × ℕ) :=
  Finset.univ.biUnion (fun s : Fin 6 =>
    (Finset.range (seedCount D (sixSeedBaseLen s))).map
      ⟨fun t => (s, t), fun _ _ h => (Prod.mk.inj h).2⟩)

/-- Constructive finite set of all six-seed trajectory iterates strictly below `6 ^ D`. -/
def familyOrbitsFinset (D : ℕ) : Finset ℕ :=
  (orbitPairsFinset D).image sixSeedMap

/-- Every `n ∈ familyOrbitsFinset D` satisfies `1 ≤ n`, `n < 6 ^ D`, and `IsLychrel6 n`. -/
theorem mem_familyOrbitsFinset_properties {D n : ℕ} (hn : n ∈ familyOrbitsFinset D) :
    1 ≤ n ∧ n < 6 ^ D ∧ IsLychrel6 n := by
  simp only [familyOrbitsFinset, orbitPairsFinset, Finset.mem_image, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Finset.mem_map, Finset.mem_range] at hn
  rcases hn with ⟨p, ⟨s, ⟨t, ht, hp_eq⟩⟩, rfl⟩
  have hp_val : p = (s, t) := hp_eq.symm
  subst hp_val
  have hp := sixSeedMap_pos_and_lychrel (s, t)
  have hlt := (sixSeedMap_length_and_lt_pow (s, t)).2
  dsimp only at ht hlt
  unfold seedCount at ht
  split_ifs at ht with hle
  · have hexp : sixSeedBaseLen s + t / 2 ≤ D := by omega
    exact ⟨hp.1, lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hexp), hp.2⟩
  · omega

/-- Exact closed-form sum for `(familyOrbitsFinset D).card` for every `D : ℕ`. -/
theorem familyOrbitsFinset_card (D : ℕ) :
    (familyOrbitsFinset D).card =
      seedCount D 110 + seedCount D 112 + seedCount D 114 +
      seedCount D 108 + seedCount D 110 + seedCount D 112 := by
  unfold familyOrbitsFinset
  rw [Finset.card_image_of_injective _ sixSeedMap_injective]
  unfold orbitPairsFinset
  rw [Finset.card_biUnion]
  · simp only [Finset.card_map, Finset.card_range]
    rw [Fin.sum_univ_six]
    rfl
  · intro s₁ _ s₂ _ hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    simp only [Finset.mem_map, Finset.mem_range] at hp₁ hp₂
    rcases hp₁ with ⟨t₁, _, hp₁_eq⟩
    rcases hp₂ with ⟨t₂, _, hp₂_eq⟩
    have h1 : (s₁, t₁) = p := hp₁_eq
    have h2 : (s₂, t₂) = p := hp₂_eq
    exact hne (Prod.mk.inj (h1.trans h2.symm)).1

/-- **Exact Linear Counting Formula**: for every `D ≥ 113`, the six disjoint trajectories contain
exactly `12 * (D - 110)` distinct base-6 Lychrel numbers strictly below `6 ^ D`
(12 distinct base-6 Lychrel numbers per additional base-6 digit). -/
theorem familyOrbitsFinset_card_of_ge {D : ℕ} (hD : 113 ≤ D) :
    (familyOrbitsFinset D).card = 12 * (D - 110) := by
  rw [familyOrbitsFinset_card]
  unfold seedCount
  by_cases h114 : 114 ≤ D
  · simp only [show 110 ≤ D by omega, show 112 ≤ D by omega, h114, show 108 ≤ D by omega,
      ↓reduceIte]
    omega
  · have hD113 : D = 113 := by omega
    subst hD113
    decide

/-- Exact count at `D = 110 + 2 * N` (`10` at `N = 0`, `26` at `N = 1`, `24 * N` for `N ≥ 2`). -/
theorem familyOrbitsFinset_card_even (N : ℕ) :
    (familyOrbitsFinset (110 + 2 * N)).card =
      if N = 0 then 10 else if N = 1 then 26 else 24 * N := by
  rcases N with _ | _ | N'
  · rw [familyOrbitsFinset_card]; decide
  · rw [familyOrbitsFinset_card]; decide
  · rw [familyOrbitsFinset_card_of_ge (by omega)]
    simp only [Nat.succ_ne_zero, ↓reduceIte, show N' + 2 ≠ 1 by omega]
    omega

/-- Exact count at full 12-step period multiples `D = 110 + 6 * k` (`10` at `k = 0`, `72 * k` for `k ≥ 1`). -/
theorem familyOrbitsFinset_card_period (k : ℕ) :
    (familyOrbitsFinset (110 + 6 * k)).card = if k = 0 then 10 else 72 * k := by
  rcases k with _ | k'
  · rw [familyOrbitsFinset_card]; decide
  · rw [familyOrbitsFinset_card_of_ge (by omega)]
    simp only [Nat.succ_ne_zero, ↓reduceIte]
    omega

/-- **Quantitative Lower Bound on Base-6 Lychrel Numbers `< 6 ^ D`** (`D ≥ 113`):
at least `12 * (D - 110)` positive integers `< 6 ^ D` are base-6 Lychrel numbers. -/
theorem lychrel6_ncard_lt_pow_ge {D : ℕ} (hD : 113 ≤ D) :
    12 * (D - 110) ≤ Set.ncard {n : ℕ | n < 6 ^ D ∧ IsLychrel6 n} := by
  have hfin : ({n : ℕ | n < 6 ^ D ∧ IsLychrel6 n}).Finite :=
    (Set.finite_lt_nat (6 ^ D)).subset (fun _ h => h.1)
  have hsub : (familyOrbitsFinset D : Set ℕ) ⊆ {n : ℕ | n < 6 ^ D ∧ IsLychrel6 n} := by
    intro n hn
    have hp := mem_familyOrbitsFinset_properties (Finset.mem_coe.mp hn)
    exact ⟨hp.2.1, hp.2.2⟩
  calc
    12 * (D - 110) = (familyOrbitsFinset D).card := (familyOrbitsFinset_card_of_ge hD).symm
    _ = ((familyOrbitsFinset D : Set ℕ)).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ Set.ncard {n : ℕ | n < 6 ^ D ∧ IsLychrel6 n} := Set.ncard_le_ncard hsub hfin

/-- **Quantitative Lower Bound on Base-6 Lychrel Numbers `≤ 6 ^ D`** (`D ≥ 113`):
at least `12 * (D - 110)` positive integers `≤ 6 ^ D` are base-6 Lychrel numbers. -/
theorem lychrel6_ncard_le_pow_ge {D : ℕ} (hD : 113 ≤ D) :
    12 * (D - 110) ≤ Set.ncard {n : ℕ | n ≤ 6 ^ D ∧ IsLychrel6 n} := by
  have hfin : ({n : ℕ | n ≤ 6 ^ D ∧ IsLychrel6 n}).Finite :=
    (Set.finite_le_nat (6 ^ D)).subset (fun _ h => h.1)
  have hsub : {n : ℕ | n < 6 ^ D ∧ IsLychrel6 n} ⊆ {n : ℕ | n ≤ 6 ^ D ∧ IsLychrel6 n} :=
    fun _ h => ⟨Nat.le_of_lt h.1, h.2⟩
  exact le_trans (lychrel6_ncard_lt_pow_ge hD) (Set.ncard_le_ncard hsub hfin)

/-- **Uniform Quantitative Lower Bound up to `6 ^ (110 + 2 * N)`** for ALL `N : ℕ`:
`max 10 (24 * N) ≤ Set.ncard {n : ℕ | n ≤ 6 ^ (110 + 2 * N) ∧ IsLychrel6 n}`. -/
theorem lychrel6_ncard_le_pow_110_add_two_mul (N : ℕ) :
    max 10 (24 * N) ≤ Set.ncard {n : ℕ | n ≤ 6 ^ (110 + 2 * N) ∧ IsLychrel6 n} := by
  have hfin : ({n : ℕ | n ≤ 6 ^ (110 + 2 * N) ∧ IsLychrel6 n}).Finite :=
    (Set.finite_le_nat (6 ^ (110 + 2 * N))).subset (fun _ h => h.1)
  have hsub : (familyOrbitsFinset (110 + 2 * N) : Set ℕ) ⊆
      {n : ℕ | n ≤ 6 ^ (110 + 2 * N) ∧ IsLychrel6 n} := by
    intro n hn
    have hp := mem_familyOrbitsFinset_properties (Finset.mem_coe.mp hn)
    exact ⟨Nat.le_of_lt hp.2.1, hp.2.2⟩
  have hcard : max 10 (24 * N) ≤ (familyOrbitsFinset (110 + 2 * N)).card := by
    rw [familyOrbitsFinset_card_even]
    split_ifs <;> omega
  calc
    max 10 (24 * N) ≤ (familyOrbitsFinset (110 + 2 * N)).card := hcard
    _ = ((familyOrbitsFinset (110 + 2 * N) : Set ℕ)).ncard := (Set.ncard_coe_finset _).symm
    _ ≤ Set.ncard {n : ℕ | n ≤ 6 ^ (110 + 2 * N) ∧ IsLychrel6 n} :=
      Set.ncard_le_ncard hsub hfin

/-- **Uniform Quantitative Lower Bound up to `6 ^ (110 + 6 * k)`** for ALL `k : ℕ`:
`max 10 (72 * k) ≤ Set.ncard {n : ℕ | n ≤ 6 ^ (110 + 6 * k) ∧ IsLychrel6 n}`. -/
theorem lychrel6_ncard_le_pow_110_add_six_mul (k : ℕ) :
    max 10 (72 * k) ≤ Set.ncard {n : ℕ | n ≤ 6 ^ (110 + 6 * k) ∧ IsLychrel6 n} := by
  have heq : 110 + 6 * k = 110 + 2 * (3 * k) := by omega
  rw [heq]
  have hmax : max 10 (72 * k) = max 10 (24 * (3 * k)) := by congr 1; omega
  rw [hmax]
  exact lychrel6_ncard_le_pow_110_add_two_mul (3 * k)

end LychrelBase6

