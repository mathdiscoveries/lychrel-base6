/-
Copyright (c) 2026 Tyler B. Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Digits.Lemmas

import Mathlib.Tactic

/-!
# Base-6 Reverse-and-Add Definitions and Digit-List Bridge (`LychrelBase6`)

Faithful natural-number definitions of base-6 digit reversal (`rev6`), reverse-and-add
(`revAdd6`), base-6 palindromes (`IsPalindrome6`), and base-6 Lychrel numbers (`IsLychrel6`),
built directly on Mathlib's canonical `Nat.digits 6` and `Nat.ofDigits 6`.

We also establish the exact correspondence between valid MSB-first base-6 digit lists and
`Nat.digits 6` / `Nat.ofDigits 6`, prove that column-by-column base-6 addition (`addLSB6Aux`
and `revAddMSB6`) faithfully computes `revAdd6`, and verify the README hand checks (`1079`
and `196` in base 6).
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
is a base-6 palindrome. This implies the `j ≥ 1` convention as an immediate corollary. -/
def IsLychrel6 (n : ℕ) : Prop :=
  ∀ j : ℕ, ¬ IsPalindrome6 (revAdd6^[j] n)

/-- Every base-6 Lychrel number under the `j ≥ 0` convention is also Lychrel under the
`j ≥ 1` convention ("never reaches a palindrome in one or more steps"). -/
theorem IsLychrel6.no_pal_pos {n : ℕ} (h : IsLychrel6 n) :
    ∀ j : ℕ, 1 ≤ j → ¬ IsPalindrome6 (revAdd6^[j] n) :=
  fun j _ => h j

/-- Evaluate a most-significant-digit-first base-6 digit list to a natural number via
`Nat.ofDigits 6`. -/
def ofDigits6MSB (ds : List ℕ) : ℕ :=
  Nat.ofDigits 6 ds.reverse

/-- Canonical validity predicate for a least-significant-digit-first base-6 digit list:
every digit is `< 6`, and if non-empty then the last (most-significant) digit is nonzero. -/
def ValidLSB6 (l : List ℕ) : Prop :=
  (∀ d ∈ l, d < 6) ∧ (∀ h : l ≠ [], l.getLast h ≠ 0)

/-- Canonical validity predicate for a non-empty most-significant-digit-first base-6 digit list:
non-empty, every digit is `< 6`, and the leading (most-significant) digit is nonzero. -/
def ValidMSB6 (ds : List ℕ) : Prop :=
  ds ≠ [] ∧ (∀ d ∈ ds, d < 6) ∧ ds.head? ≠ some 0

instance decidableValidMSB6 (ds : List ℕ) : Decidable (ValidMSB6 ds) := by
  unfold ValidMSB6
  infer_instance

/-- Reversing a valid MSB-first base-6 digit list yields a valid LSB-first base-6 digit list. -/
theorem ValidMSB6.validLSB6_reverse {ds : List ℕ} (h : ValidMSB6 ds) : ValidLSB6 ds.reverse := by
  rcases h with ⟨hne, hlt, hhead⟩
  refine ⟨?_, ?_⟩
  · intro d hd
    exact hlt d (List.mem_reverse.mp hd)
  · intro hrev
    cases ds with
    | nil => exact (hne rfl).elim
    | cons a tl =>
      simp only [List.reverse_cons, List.getLast_append_singleton]
      intro ha
      apply hhead
      simp [ha]

/-- `Nat.digits 6` is the exact left inverse of `Nat.ofDigits 6` on valid LSB-first lists. -/
theorem digits_ofDigits_validLSB6 {l : List ℕ} (hl : ValidLSB6 l) :
    Nat.digits 6 (Nat.ofDigits 6 l) = l :=
  Nat.digits_ofDigits 6 (by norm_num) l hl.1 hl.2

/-- `Nat.digits 6` recovers `ds.reverse` from `ofDigits6MSB ds` for any valid MSB-first list. -/
theorem digits_ofDigits6MSB {ds : List ℕ} (hds : ValidMSB6 ds) :
    Nat.digits 6 (ofDigits6MSB ds) = ds.reverse :=
  digits_ofDigits_validLSB6 hds.validLSB6_reverse

/-- On a valid MSB-first list `ds`, `rev6 (ofDigits6MSB ds)` evaluates `ds` in LSB-first order. -/
theorem rev6_ofDigits6MSB {ds : List ℕ} (hds : ValidMSB6 ds) :
    rev6 (ofDigits6MSB ds) = Nat.ofDigits 6 ds := by
  unfold rev6
  rw [digits_ofDigits6MSB hds, List.reverse_reverse]

/-- A valid MSB-first digit list represents a base-6 palindrome iff it equals its reversal. -/
theorem isPalindrome6_ofDigits6MSB {ds : List ℕ} (hds : ValidMSB6 ds) :
    IsPalindrome6 (ofDigits6MSB ds) ↔ ds.reverse = ds := by
  unfold IsPalindrome6
  rw [digits_ofDigits6MSB hds, List.reverse_reverse]
  exact eq_comm

/-- `ofDigits6MSB` is injective on valid MSB-first base-6 digit lists. -/
theorem ofDigits6MSB_inj {ds₁ ds₂ : List ℕ} (h₁ : ValidMSB6 ds₁) (h₂ : ValidMSB6 ds₂)
    (heq : ofDigits6MSB ds₁ = ofDigits6MSB ds₂) : ds₁ = ds₂ := by
  have hd : Nat.digits 6 (ofDigits6MSB ds₁) = Nat.digits 6 (ofDigits6MSB ds₂) :=
    congrArg (Nat.digits 6) heq
  rw [digits_ofDigits6MSB h₁, digits_ofDigits6MSB h₂] at hd
  exact List.reverse_injective hd

/-- Value of `Nat.ofDigits 6` on a list concatenation `l₁ ++ l₂`. -/
theorem ofDigits6_append (l₁ l₂ : List ℕ) :
    Nat.ofDigits 6 (l₁ ++ l₂) = Nat.ofDigits 6 l₁ + 6 ^ l₁.length * Nat.ofDigits 6 l₂ := by
  induction l₁ with
  | nil => simp
  | cons a tl ih =>
    simp only [List.cons_append, Nat.ofDigits_cons, List.length_cons, ih, pow_succ']
    ring

/-- Upper bound: any LSB-first list `l` with digits `< 6` satisfies `Nat.ofDigits 6 l < 6 ^ l.length`. -/
theorem ofDigits6_lt_pow_length {l : List ℕ} (hlt : ∀ d ∈ l, d < 6) :
    Nat.ofDigits 6 l < 6 ^ l.length := by
  induction l with
  | nil => simp
  | cons a tl ih =>
    have ha : a < 6 := hlt a (List.mem_cons_self ..)
    have htl : Nat.ofDigits 6 tl < 6 ^ tl.length :=
      ih (fun d hd => hlt d (List.mem_cons_of_mem a hd))
    simp only [Nat.ofDigits_cons, List.length_cons, pow_succ']
    omega

/-- Lower bound: any valid MSB-first list `ds` satisfies `6 ^ (ds.length - 1) ≤ ofDigits6MSB ds`. -/
theorem pow_length_sub_one_le_ofDigits6MSB {ds : List ℕ} (hds : ValidMSB6 ds) :
    6 ^ (ds.length - 1) ≤ ofDigits6MSB ds := by
  rcases hds with ⟨hne, _, hhead⟩
  cases ds with
  | nil => exact (hne rfl).elim
  | cons a tl =>
    have ha : 1 ≤ a := by
      have ha0 : a ≠ 0 := fun h => hhead (by simp [h])
      omega
    unfold ofDigits6MSB
    rw [List.reverse_cons, ofDigits6_append]
    simp only [List.length_cons, Nat.add_sub_cancel, List.length_reverse,
      Nat.ofDigits_singleton]
    have hmul : 6 ^ tl.length * 1 ≤ 6 ^ tl.length * a := Nat.mul_le_mul_left _ ha
    omega

/-- Strict length monotonicity: shorter valid MSB-first base-6 digit lists represent strictly
smaller natural numbers than longer ones. -/
theorem ofDigits6MSB_lt_of_length_lt {ds₁ ds₂ : List ℕ} (h₁ : ValidMSB6 ds₁) (h₂ : ValidMSB6 ds₂)
    (hlen : ds₁.length < ds₂.length) :
    ofDigits6MSB ds₁ < ofDigits6MSB ds₂ := by
  have hupper : ofDigits6MSB ds₁ < 6 ^ ds₁.length := by
    unfold ofDigits6MSB
    have h := ofDigits6_lt_pow_length (fun d hd => h₁.2.1 d (List.mem_reverse.mp hd))
    simpa only [List.length_reverse] using h
  have hlower : 6 ^ (ds₂.length - 1) ≤ ofDigits6MSB ds₂ :=
    pow_length_sub_one_le_ofDigits6MSB h₂
  have hpow : 6 ^ ds₁.length ≤ 6 ^ (ds₂.length - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- Column-by-column base-6 addition of two equal-length LSB-first digit lists with incoming
carry `c`, returning `(sumDigitsLSB, carryOut)`. -/
def addLSB6Aux : List ℕ → List ℕ → ℕ → List ℕ × ℕ
  | [], [], c => ([], c)
  | a :: as, b :: bs, c =>
    let s := a + b + c
    let res := addLSB6Aux as bs (s / 6)
    (s % 6 :: res.1, res.2)
  | _, _, c => ([], c)

/-- Arithmetic soundness of `addLSB6Aux`: the base-6 value of the output digits plus the
shifted carry-out equals the sum of the two inputs plus the incoming carry. -/
theorem ofDigits6_addLSB6Aux :
    ∀ (as bs : List ℕ) (c : ℕ), as.length = bs.length →
      Nat.ofDigits 6 (addLSB6Aux as bs c).1 + (addLSB6Aux as bs c).2 * 6 ^ as.length =
        Nat.ofDigits 6 as + Nat.ofDigits 6 bs + c
  | [], [], c, _ => by simp [addLSB6Aux]
  | a :: as, b :: bs, c, hlen => by
    have hlen' : as.length = bs.length := by simpa using hlen
    have ih := ofDigits6_addLSB6Aux as bs ((a + b + c) / 6) hlen'
    have hdiv : (a + b + c) % 6 + 6 * ((a + b + c) / 6) = a + b + c := by omega
    simp only [addLSB6Aux, Nat.ofDigits_cons, List.length_cons, pow_succ']
    linarith
  | [], _ :: _, _, hlen => by simp at hlen
  | _ :: _, [], _, hlen => by simp at hlen

/-- `addLSB6Aux` preserves the list length on equal-length inputs. -/
theorem addLSB6Aux_length :
    ∀ (as bs : List ℕ) (c : ℕ), as.length = bs.length →
      (addLSB6Aux as bs c).1.length = as.length
  | [], [], _, _ => by simp [addLSB6Aux]
  | a :: as, b :: bs, c, hlen => by
    have hlen' : as.length = bs.length := by simpa using hlen
    simp [addLSB6Aux, addLSB6Aux_length as bs ((a + b + c) / 6) hlen']
  | [], _ :: _, _, hlen => by simp at hlen
  | _ :: _, [], _, hlen => by simp at hlen

/-- Every digit produced by `addLSB6Aux` is strictly less than `6`. -/
theorem addLSB6Aux_digits_lt :
    ∀ (as bs : List ℕ) (c : ℕ) (d : ℕ), d ∈ (addLSB6Aux as bs c).1 → d < 6
  | [], [], _, _, hd => by simp [addLSB6Aux] at hd
  | a :: as, b :: bs, c, d, hd => by
    simp only [addLSB6Aux, List.mem_cons] at hd
    rcases hd with rfl | hd'
    · omega
    · exact addLSB6Aux_digits_lt as bs ((a + b + c) / 6) d hd'
  | [], _ :: _, _, _, hd => by simp [addLSB6Aux] at hd
  | _ :: _, [], _, _, hd => by simp [addLSB6Aux] at hd

/-- If all input digits are `< 6` and the incoming carry is `≤ 1`, then the carry-out of
`addLSB6Aux` is `≤ 1`. -/
theorem addLSB6Aux_carry_le :
    ∀ (as bs : List ℕ) (c : ℕ), as.length = bs.length →
      (∀ d ∈ as, d < 6) → (∀ d ∈ bs, d < 6) → c ≤ 1 →
      (addLSB6Aux as bs c).2 ≤ 1
  | [], [], c, _, _, _, hc => by simpa [addLSB6Aux] using hc
  | a :: as, b :: bs, c, hlen, has, hbs, hc => by
    have hlen' : as.length = bs.length := by simpa using hlen
    have ha : a < 6 := has a (List.mem_cons_self ..)
    have hb : b < 6 := hbs b (List.mem_cons_self ..)
    have hc' : (a + b + c) / 6 ≤ 1 := by omega
    exact addLSB6Aux_carry_le as bs ((a + b + c) / 6) hlen'
      (fun d hd => has d (List.mem_cons_of_mem a hd))
      (fun d hd => hbs d (List.mem_cons_of_mem b hd)) hc'
  | [], _ :: _, _, hlen, _, _, _ => by simp at hlen
  | _ :: _, [], _, hlen, _, _, _ => by simp at hlen

/-- Block composition law for `addLSB6Aux`: adding concatenated equal-length blocks threads the
carry from the lower block into the upper block. -/
theorem addLSB6Aux_append :
    ∀ (as₁ bs₁ as₂ bs₂ : List ℕ) (c : ℕ),
      as₁.length = bs₁.length →
      addLSB6Aux (as₁ ++ as₂) (bs₁ ++ bs₂) c =
        let r₁ := addLSB6Aux as₁ bs₁ c
        let r₂ := addLSB6Aux as₂ bs₂ r₁.2
        (r₁.1 ++ r₂.1, r₂.2)
  | [], [], as₂, bs₂, c, _ => by simp [addLSB6Aux]
  | a :: as₁, b :: bs₁, as₂, bs₂, c, hlen => by
    have hlen' : as₁.length = bs₁.length := by simpa using hlen
    have ih := addLSB6Aux_append as₁ bs₁ as₂ bs₂ ((a + b + c) / 6) hlen'
    simp only [List.cons_append, addLSB6Aux, ih]
  | [], _ :: _, _, _, _, hlen => by simp at hlen
  | _ :: _, [], _, _, _, hlen => by simp at hlen

/-- Finalize `(sumLSB, carry)` into an MSB-first base-6 digit list. -/
def finishMSB6 : List ℕ × ℕ → List ℕ
  | (sumLSB, 0) => sumLSB.reverse
  | (sumLSB, c + 1) => (c + 1) :: sumLSB.reverse

/-- Pure digit-list base-6 reverse-and-add on an MSB-first list `ds`. -/
def revAddMSB6 (ds : List ℕ) : List ℕ :=
  finishMSB6 (addLSB6Aux ds.reverse ds 0)

/-- `ofDigits6MSB (revAddMSB6 ds)` equals `revAdd6 (ofDigits6MSB ds)` for every valid
MSB-first base-6 digit list `ds`. -/
theorem ofDigits6MSB_revAddMSB6 {ds : List ℕ} (hds : ValidMSB6 ds) :
    ofDigits6MSB (revAddMSB6 ds) = revAdd6 (ofDigits6MSB ds) := by
  have hlen : ds.reverse.length = ds.length := List.length_reverse
  have hval := ofDigits6_addLSB6Aux ds.reverse ds 0 hlen
  have hreslen : (addLSB6Aux ds.reverse ds 0).1.length = ds.length := by
    rw [addLSB6Aux_length ds.reverse ds 0 hlen, List.length_reverse]
  unfold revAddMSB6 revAdd6
  rw [rev6_ofDigits6MSB hds]
  unfold ofDigits6MSB at hval ⊢
  rcases hres : addLSB6Aux ds.reverse ds 0 with ⟨sumLSB, carry⟩
  rw [hres] at hval hreslen
  cases carry with
  | zero =>
    simp only [finishMSB6, List.reverse_reverse]
    simp only [zero_mul, add_zero] at hval
    exact hval
  | succ c =>
    simp only [finishMSB6]
    rw [List.reverse_cons, ofDigits6_append, List.reverse_reverse, hreslen,
      Nat.ofDigits_singleton]
    rw [List.length_reverse, add_zero] at hval
    linarith

/-- `revAddMSB6` preserves `ValidMSB6`: adding a positive valid base-6 number to its reversal
always produces a non-empty valid MSB-first digit list with no leading zero. -/
theorem revAddMSB6_valid {ds : List ℕ} (hds : ValidMSB6 ds) : ValidMSB6 (revAddMSB6 ds) := by
  have hlen : ds.reverse.length = ds.length := List.length_reverse
  have hreslen : (addLSB6Aux ds.reverse ds 0).1.length = ds.length := by
    rw [addLSB6Aux_length ds.reverse ds 0 hlen, List.length_reverse]
  have hcarry : (addLSB6Aux ds.reverse ds 0).2 ≤ 1 :=
    addLSB6Aux_carry_le ds.reverse ds 0 hlen
      (fun d hd => hds.2.1 d (List.mem_reverse.mp hd)) hds.2.1 (by omega)
  have hdigits : ∀ d ∈ (addLSB6Aux ds.reverse ds 0).1, d < 6 :=
    addLSB6Aux_digits_lt ds.reverse ds 0
  have hval : ofDigits6MSB (revAddMSB6 ds) = revAdd6 (ofDigits6MSB ds) :=
    ofDigits6MSB_revAddMSB6 hds
  unfold revAddMSB6 at hval ⊢
  rcases hres : addLSB6Aux ds.reverse ds 0 with ⟨sumLSB, carry⟩
  rw [hres] at hreslen hcarry hdigits hval
  cases carry with
  | zero =>
    simp only [finishMSB6] at hval ⊢
    refine ⟨?_, ?_, ?_⟩
    · intro hempty
      have h0 : sumLSB.length = 0 := by
        simpa using congrArg List.length hempty
      rw [hreslen] at h0
      exact hds.1 (List.eq_nil_of_length_eq_zero h0)
    · intro d hd
      exact hdigits d (List.mem_reverse.mp hd)
    · intro hhead
      cases hrev : sumLSB.reverse with
      | nil => simp [hrev] at hhead
      | cons a tl =>
        rw [hrev] at hhead hval
        have ha0 : a = 0 := by simpa using hhead
        subst ha0
        have htl_len : tl.length = ds.length - 1 := by
          have h1 : (0 :: tl).length = ds.length := by
            rw [← hrev, List.length_reverse, hreslen]
          simp at h1
          omega
        have hupper : ofDigits6MSB (0 :: tl) < 6 ^ (ds.length - 1) := by
          unfold ofDigits6MSB
          rw [List.reverse_cons, ofDigits6_append]
          simp only [Nat.ofDigits_singleton, mul_zero, add_zero]
          have hlt_tl : ∀ d ∈ tl.reverse, d < 6 := by
            intro d hd
            have hd' : d ∈ (0 :: tl) := List.mem_cons_of_mem 0 (List.mem_reverse.mp hd)
            rw [← hrev] at hd'
            exact hdigits d (List.mem_reverse.mp hd')
          have hlt := ofDigits6_lt_pow_length hlt_tl
          rwa [List.length_reverse, htl_len] at hlt
        have hlower : 6 ^ (ds.length - 1) ≤ ofDigits6MSB ds :=
          pow_length_sub_one_le_ofDigits6MSB hds
        unfold revAdd6 at hval
        omega
  | succ c =>
    simp only [finishMSB6]
    refine ⟨List.cons_ne_nil _ _, ?_, ?_⟩
    · intro d hd
      simp only [List.mem_cons] at hd
      rcases hd with rfl | hd'
      · omega
      · exact hdigits d (List.mem_reverse.mp hd')
    · simp

/-- Column-by-column digit addition computes `Nat.digits 6 (revAdd6 (ofDigits6MSB ds))`. -/
theorem digits_revAdd6_ofDigits6MSB {ds : List ℕ} (hds : ValidMSB6 ds) :
    Nat.digits 6 (revAdd6 (ofDigits6MSB ds)) = (revAddMSB6 ds).reverse := by
  rw [← ofDigits6MSB_revAddMSB6 hds, digits_ofDigits6MSB (revAddMSB6_valid hds)]

/-- Iterated `revAddMSB6` preserves `ValidMSB6`. -/
theorem revAddMSB6_iterate_valid {ds : List ℕ} (hds : ValidMSB6 ds) :
    ∀ t : ℕ, ValidMSB6 (revAddMSB6^[t] ds)
  | 0 => hds
  | t + 1 => by
    rw [Function.iterate_succ_apply']
    exact revAddMSB6_valid (revAddMSB6_iterate_valid hds t)

/-- Iterated `revAdd6` on `ofDigits6MSB ds` equals `ofDigits6MSB` of iterated `revAddMSB6`. -/
theorem revAdd6_iterate_ofDigits6MSB {ds : List ℕ} (hds : ValidMSB6 ds) :
    ∀ t : ℕ, revAdd6^[t] (ofDigits6MSB ds) = ofDigits6MSB (revAddMSB6^[t] ds)
  | 0 => rfl
  | t + 1 => by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      revAdd6_iterate_ofDigits6MSB hds t,
      ← ofDigits6MSB_revAddMSB6 (revAddMSB6_iterate_valid hds t)]

/-- Palindrome test on any iterate `revAdd6^[t] (ofDigits6MSB ds)` reduces to list reversal
equality on `revAddMSB6^[t] ds`. -/
theorem isPalindrome6_revAdd6_iterate_ofDigits6MSB {ds : List ℕ} (hds : ValidMSB6 ds) (t : ℕ) :
    IsPalindrome6 (revAdd6^[t] (ofDigits6MSB ds)) ↔
      (revAddMSB6^[t] ds).reverse = revAddMSB6^[t] ds := by
  rw [revAdd6_iterate_ofDigits6MSB hds t,
    isPalindrome6_ofDigits6MSB (revAddMSB6_iterate_valid hds t)]

/-! ### Hand checks from the README (`1079 = 4555_6` and `196 = 524_6`) -/

/-- `1079 = 4555_6`, `rev6 1079 = 5554_6 = 1294`, and `revAdd6 1079 = 2373 = 14553_6`. -/
theorem revAdd6_1079 : revAdd6 1079 = 2373 := by
  have hvalid : ValidMSB6 [4, 5, 5, 5] := by decide
  have h1079 : ofDigits6MSB [4, 5, 5, 5] = 1079 := by decide
  rw [← h1079, ← ofDigits6MSB_revAddMSB6 hvalid]
  decide

/-- `rev6 1079 = 1294` (`5554_6`). -/
theorem rev6_1079 : rev6 1079 = 1294 := by
  have hvalid : ValidMSB6 [4, 5, 5, 5] := by decide
  have h1079 : ofDigits6MSB [4, 5, 5, 5] = 1079 := by decide
  rw [← h1079, rev6_ofDigits6MSB hvalid]
  decide

/-- `Nat.digits 6 2373 = [3, 5, 5, 4, 1]` (`14553_6` in LSB-first order). -/
theorem digits6_2373 : Nat.digits 6 2373 = [3, 5, 5, 4, 1] := by
  have hvalid : ValidMSB6 [1, 4, 5, 5, 3] := by decide
  have h2373 : ofDigits6MSB [1, 4, 5, 5, 3] = 2373 := by decide
  rw [← h2373, digits_ofDigits6MSB hvalid]
  rfl

/-- `196 = 524_6` reaches the base-6 palindrome `44044_6 = 6076` in 4 reverse-and-add steps. -/
theorem revAdd6_four_196 : revAdd6^[4] 196 = 6076 := by
  have hvalid : ValidMSB6 [5, 2, 4] := by decide
  have h196 : ofDigits6MSB [5, 2, 4] = 196 := by decide
  rw [← h196, revAdd6_iterate_ofDigits6MSB hvalid 4]
  decide

/-- `196` becomes a base-6 palindrome after 4 steps (`44044_6`). -/
theorem isPalindrome6_revAdd6_four_196 : IsPalindrome6 (revAdd6^[4] 196) := by
  have hvalid : ValidMSB6 [5, 2, 4] := by decide
  have h196 : ofDigits6MSB [5, 2, 4] = 196 := by decide
  rw [← h196, isPalindrome6_revAdd6_iterate_ofDigits6MSB hvalid 4]
  decide

end LychrelBase6
