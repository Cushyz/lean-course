import Dihedral.Basic

open DihedralGroup CoxeterSystem List

@[simp] lemma zmod0_cast_add_int (a b : ZMod 0) :
    (((a + b).cast : Int) = (a.cast : Int) + (b.cast : Int)) := by
  rw [ZMod.cast_add (dvd_refl 0)]

@[simp] lemma zmod0_cast_sub_int (a b : ZMod 0) :
    (((a - b).cast : Int) = (a.cast : Int) - (b.cast : Int)) := by
  rw [ZMod.cast_sub (dvd_refl 0)]

@[simp] lemma zmod0_cast_neg_int (a : ZMod 0) :
    (((-a).cast : Int) = -(a.cast : Int)) := by
  rw [ZMod.cast_neg (dvd_refl 0)]

@[simp] lemma zmod0_cast_intCast_int (k : Int) :
    (((k : ZMod 0).cast : Int) = k) := by
  simp

@[simp] lemma zmod0_cast_natCast_int (k : Nat) :
    (((k : ZMod 0).cast : Int) = k) := by
  rw [ZMod.cast_natCast (dvd_refl 0)]

@[simp] lemma zmod0_cast_one_int :
    (((1 : ZMod 0).cast : Int) = 1) := by
  rw [ZMod.cast_one (dvd_refl 0)]

@[simp] lemma zmod0_intCast_cast (k : ZMod 0) :
    (((k.cast : Int) : ZMod 0) = k) :=
  ZMod.intCast_zmod_cast k

lemma int_natAbs_natCast_div_two (n : Nat) :
    Int.natAbs ((n : Int) / 2) = n / 2 := by
  omega

def reducedWord (g : D∞) : List (Fin 2) :=
    match g with
    | r k =>
      let k_int : ℤ := k.cast
      if k_int ≥ 0 then
        CoxeterSystem.alternatingWord 0 1 (2 * k_int.natAbs)
      else
        CoxeterSystem.alternatingWord 1 0 (2 * k_int.natAbs)
    | sr k =>
      let k_int : ℤ := k.cast
      if k_int > 0 then
        CoxeterSystem.alternatingWord 0 1 (2 * k_int.natAbs - 1)
      else
        CoxeterSystem.alternatingWord 1 0 (2 * k_int.natAbs + 1)
-- Helper function: the expected length of an element of D∞
def explicit_length : D∞ → ℕ
| r k => 2 * (k.cast : ℤ).natAbs
| sr k =>
  let k_int : ℤ := k.cast
  if k_int > 0 then
    2 * k_int.natAbs - 1
  else
    2 * k_int.natAbs + 1

lemma explicit_length_mul_le (i : Fin 2) (g : D∞) :
    explicit_length (f i * g) ≤ explicit_length g + 1 := by
  fin_cases i
  · -- multiplying by s0 (f 0)
    simp only [f, s0]
    cases g with
    | r k =>
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, sr_mul_r, zero_add]
      dsimp [explicit_length]
      split_ifs with h
      · apply Nat.le_succ_of_le
        simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
      · apply le_refl
    | sr k =>
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, sr_mul_sr, sub_zero]
      dsimp [explicit_length]
      split_ifs with h
      · rw [Nat.sub_add_cancel]
        have hk : 1 ≤ Int.natAbs (k.cast : ℤ) := by
          have : Int.natAbs (k.cast : ℤ) > 0 := Int.natAbs_pos.mpr (ne_of_gt h)
          omega
        omega
      · apply Nat.le_succ_of_le
        apply Nat.le_succ
  · simp only [f, s1]
    cases g with
    | r k =>
      have h_s1 : sr (1 : ZMod 0) = sr 0 * r 1 := by simp [sr_mul_r]
      rw [h_s1, sr_mul_r, zero_add]
      dsimp [explicit_length]
      let k_int : ℤ := k.cast
      by_cases hk : k_int ≥ 0
      · have h_pos : 1 + k_int > 0 := by omega
        rw [if_pos (by simpa [k_int] using h_pos)]
        have : ((1 + k).cast : ℤ).natAbs = 1 + (k.cast : ℤ).natAbs := by
          rw [zmod0_cast_add_int, zmod0_cast_one_int]; omega
        rw [this]; omega
      · push Not at hk
        by_cases hk1 : k = -1
        · subst hk1; simp
        · have h_nonpos : 1 + k_int ≤ 0 := by omega
          rw [if_neg (by simpa [k_int] using not_lt.mpr h_nonpos)]
          have : ((1 + k).cast : ℤ).natAbs = (k.cast : ℤ).natAbs - 1 := by
            rw [zmod0_cast_add_int, zmod0_cast_one_int]; omega
          rw [this]; omega
    | sr k =>
      dsimp [explicit_length]
      split_ifs with h
      · let k_int : ℤ := k.cast
        have : ((k - 1).cast : ℤ).natAbs = (k.cast : ℤ).natAbs - 1 := by
          have h1 : 1 ≤ k_int := Int.add_one_le_iff.mpr h
          rw [zmod0_cast_sub_int, zmod0_cast_one_int]; omega
        rw [this]; omega
      · let k_int : ℤ := k.cast
        have h_le : k_int ≤ 0 := Int.not_lt.mp h
        have h_abs : ((k - 1).cast : ℤ).natAbs = (k.cast : ℤ).natAbs + 1 := by
          rw [zmod0_cast_sub_int, zmod0_cast_one_int]; omega
        rw [h_abs]
        omega

lemma cs_length_ge_explicit (g : D∞) : explicit_length g ≤ ℓ g := by
  have h_bound (L : List (Fin 2)) : explicit_length (cs.wordProd L) ≤ L.length := by
    induction L with
    | nil => simp [cs.wordProd_nil, explicit_length]; rfl
    | cons i L ih =>
      simp only [List.length_cons, CoxeterSystem.wordProd_cons]
      have h_simple : cs.simple i = f i := by fin_cases i <;> rfl
      rw [h_simple]
      apply le_trans (explicit_length_mul_le i (cs.wordProd L))
      exact Nat.add_le_add_right ih 1
  obtain ⟨L, hL_red, hL_prod⟩ := cs.exists_isReduced g
  rw [hL_prod, hL_red.eq]
  exact h_bound L

-- reducedWord reconstructs the group element
lemma reducedWord_correct (g : D∞) : cs.wordProd (reducedWord g) = g := by
  cases g with
  | r k =>
    dsimp [reducedWord]
    split_ifs with h
    · -- k ≥ 0. alternatingWord 0 1 (2k)
      rw [cs.prod_alternatingWord_eq_mul_pow 0 1 (2 * (k.cast : ℤ).natAbs)]
      simp only [even_two, Even.mul_right, ↓reduceIte, Fin.isValue, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, mul_div_cancel_left₀, one_mul]
      change (s0 * s1) ^ Int.natAbs (k.cast : ℤ) = r k
      simp only [s0, s1, sr_mul_sr, sub_zero, r_pow,  one_mul, r.injEq]
      exact Int.natAbs_of_nonneg h
    · -- k < 0. alternatingWord 1 0 (2|k|)
      rw [cs.prod_alternatingWord_eq_mul_pow 1 0 (2 * (k.cast : ℤ).natAbs)]
      simp only [even_two, Even.mul_right, ↓reduceIte, Fin.isValue, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, mul_div_cancel_left₀, one_mul]
      change (s1 * s0) ^ Int.natAbs (k.cast : ℤ) = r k
      simp only [s1, s0, sr_mul_sr, zero_sub, r_pow, neg_mul, one_mul, r.injEq]
      have : -(((k.cast : ℤ).natAbs) : ℤ) = k.cast := by omega
      change ((-(((k.cast : ℤ).natAbs) : ℤ) : ZMod 0) = k)
      rw [this]
      simp
  | sr k =>
    dsimp [reducedWord]
    split_ifs with h
    · -- k > 0. alternatingWord 0 1 (2k - 1). Odd.
      rw [cs.prod_alternatingWord_eq_mul_pow 0 1 (2 * (k.cast : ℤ).natAbs - 1)]
      have h_odd : ¬ Even (2 * (k.cast : ℤ).natAbs - 1) := by
        rw [Nat.not_even_iff_odd]; use ((k.cast : ℤ).natAbs - 1); omega
      simp only [h_odd, ↓reduceIte]
      have h_div : (2 * (k.cast : ℤ).natAbs - 1) / 2 = (k.cast : ℤ).natAbs - 1 := by omega
      rw [h_div, ← s0', ← s1']
      simp only [s1, s0, sr_mul_sr, sub_zero, r_pow, one_mul, sr_mul_r, sr.injEq]
      have h_int :
          (1 : ℤ) + ↑(Int.natAbs (k.cast : ℤ) - 1) = k.cast := by omega
      change (((1 : ℤ) + ↑(Int.natAbs (k.cast : ℤ) - 1) : ℤ) : ZMod 0) = k
      rw [h_int]
      simp
    · -- k ≤ 0. alternatingWord 1 0 (2|k| + 1). Odd.
      rw [cs.prod_alternatingWord_eq_mul_pow 1 0 (2 * (k.cast : ℤ).natAbs + 1)]
      have h_odd : ¬ Even (2 * (k.cast : ℤ).natAbs + 1) := by simp only [Nat.not_even_bit1, not_false_eq_true]
      simp only [h_odd, ↓reduceIte]
      have h_div : (2 * (k.cast : ℤ).natAbs + 1) / 2 = (k.cast : ℤ).natAbs := by omega
      rw [h_div, ← s1', ← s0']
      simp only [s0, s1, sr_mul_sr, zero_sub, r_pow, neg_mul, one_mul, sr_mul_r,
        zero_add, sr.injEq]
      have h_int : (↑(Int.natAbs (k.cast : ℤ)) : ℤ) = -k.cast :=
        Int.ofNat_natAbs_of_nonpos (not_lt.mp h)
      change ((-↑(Int.natAbs (k.cast : ℤ)) : ℤ) : ZMod 0) = k
      rw [h_int, neg_neg]
      simp

-- explicit_length agrees with the length of alternatingWord; note that the
-- definition of alternatingWord imposes no alternation condition
lemma explicit_length_alternatingWord (i j : Fin 2) (n : ℕ) (h_ne : i ≠ j) :
    explicit_length (cs.wordProd (CoxeterSystem.alternatingWord i j n)) = n := by
  -- Using the identity wordProd (reducedWord g) = g in reverse
  rw [cs.prod_alternatingWord_eq_mul_pow]
  split_ifs with h_even
  · -- Even n
    simp only [one_mul]
    fin_cases i <;> fin_cases j
    · -- i=0, j=0
      contradiction
    · -- i=0, j=1
      simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, ← s0', ← s1', s0, s1, sr_mul_sr,
        sub_zero, r_pow, one_mul]
      dsimp [explicit_length]
      have hdiv : 2 * (n / 2) = n := by
        simpa [Nat.mul_comm] using (Nat.div_mul_cancel (h_even.two_dvd))
      have h_abs : Int.natAbs (((n / 2 : ℕ) : ZMod 0).cast : ℤ) = n / 2 := by
        exact int_natAbs_natCast_div_two n
      rw [h_abs]
      exact hdiv
    · -- i=1, j=0.
      simp only [explicit_length, Fin.mk_one, Fin.isValue, ← s1', s1, Fin.zero_eta, ← s0', s0,
        sr_mul_sr, zero_sub, r_pow, neg_mul, one_mul]
      simp only [zmod0_cast_neg_int, zmod0_cast_natCast_int]
      have hdiv : 2 * (n / 2) = n := by
        simpa [Nat.mul_comm] using (Nat.div_mul_cancel (h_even.two_dvd))
      omega
    · -- i=1, j=1
      contradiction
  · -- Odd n
    rw [Nat.not_even_iff_odd] at h_even
    let m := n / 2
    fin_cases i <;> fin_cases j
    · -- i=0, j=0
      contradiction
    · -- i=0, j=1
      simp only [explicit_length, Fin.mk_one, Fin.isValue, ← s1', s1, Fin.zero_eta, ← s0', s0,
        sr_mul_sr, sub_zero, r_pow, one_mul, sr_mul_r, gt_iff_lt]
      norm_cast
      simp only [add_pos_iff, zero_lt_one, Nat.div_pos_iff, Nat.ofNat_pos, true_and, true_or,
        ↓reduceIte]
      have h : 2 * (n / 2) + 1 = n :=
        Nat.two_mul_div_two_add_one_of_odd h_even
      omega
    · -- i=1, j=0.
      simp only [explicit_length, Fin.zero_eta, Fin.isValue, ← s0', s0, Fin.mk_one, ← s1', s1,
        sr_mul_sr, zero_sub, r_pow, neg_mul, one_mul, sr_mul_r, zero_add, gt_iff_lt,
        ]
      split_ifs with h_pos
      · simp at h_pos
        omega
      · simp only [zmod0_cast_neg_int, zmod0_cast_natCast_int]
        have hodd : 2 * (n / 2) + 1 = n :=
          Nat.two_mul_div_two_add_one_of_odd h_even
        omega
    · -- i=1, j=1
      contradiction

lemma alternating_reducedWord (i i' : Fin 2) (n : ℕ) (h_ne : i ≠ i') :
    reducedWord (cs.wordProd (alternatingWord i i' n)) = alternatingWord i i' n := by
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · -- n = 2 * k
    fin_cases i <;> fin_cases i'
    · contradiction
    · -- i=0, i'=1. g = (s0 s1)^k = r k.
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, cs.prod_alternatingWord_eq_mul_pow,
        Even.add_self, ↓reduceIte, one_mul, ← s0', ← s1', s0, s1, sr_mul_sr, sub_zero, r_pow,
        reducedWord, ge_iff_le, zmod0_cast_natCast_int]
      rw [if_pos (by omega)]
      congr
      omega
    · -- i=1, i'=0. g = (s1 s0)^k = r (-k).
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, cs.prod_alternatingWord_eq_mul_pow,
        Even.add_self, ↓reduceIte, one_mul, ← s0', ← s1', s0, s1, sr_mul_sr, zero_sub, r_pow,
        neg_mul, reducedWord, ge_iff_le, zmod0_cast_neg_int, zmod0_cast_natCast_int]
      by_cases hk : k = 0
      · subst hk
        simp [alternatingWord]
      · rw [if_neg (by omega)]
        congr
        omega
    · contradiction
  · -- n = 2 * k + 1
    fin_cases i <;> fin_cases i'
    · contradiction
    · -- i=0, i'=1.
      simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, cs.prod_alternatingWord_eq_mul_pow,
        Nat.not_even_bit1, ↓reduceIte]
      have h_div : (2 * k + 1) / 2 = k := by omega
      rw [h_div]
      let k_int : ℤ := k
      simp only [reducedWord, Fin.isValue, ← s1', s1, ← s0', s0, sr_mul_sr, sub_zero, r_pow,
        one_mul, sr_mul_r, gt_iff_lt]
      have : (1 + k_int) > 0 := by norm_cast; omega
      rw [if_pos (by simpa [k_int] using this)]
      congr 1
      simp only [zmod0_cast_add_int, zmod0_cast_one_int, zmod0_cast_natCast_int]
      omega
    · -- i=1, i'=0.
      simp only [Fin.mk_one, Fin.isValue, Fin.zero_eta, cs.prod_alternatingWord_eq_mul_pow,
        Nat.not_even_bit1, ↓reduceIte]
      have h_div : (2 * k + 1) / 2 = k := by omega
      rw [h_div]
      simp only [reducedWord, Fin.isValue, ← s0', s0, ← s1', s1, sr_mul_sr, zero_sub, r_pow,
        neg_mul, one_mul, sr_mul_r, zero_add, gt_iff_lt]
      let k_int : ℤ := k
      have : ((k) : ℤ) ≥ 0 := by norm_cast; omega
      rw [if_neg (by simp)]
      congr 1
      simp only [zmod0_cast_neg_int, zmod0_cast_natCast_int]
      omega
    · contradiction

theorem length_eq (g : D∞) : ℓ g = (reducedWord g).length := by
  have h_prod : cs.wordProd (reducedWord g) = g := reducedWord_correct g
  have h_le : ℓ g ≤ (reducedWord g).length := by
    nth_rewrite 1 [← h_prod]
    exact cs.length_wordProd_le (reducedWord g)
  have h_len_eq : (reducedWord g).length = explicit_length g := by
    cases g with
    | r k =>
      dsimp [reducedWord]
      split_ifs
      <;>
      · rw [CoxeterSystem.length_alternatingWord]
        dsimp [explicit_length]
    | sr k =>
      dsimp [reducedWord]
      split_ifs with h
      · rw [CoxeterSystem.length_alternatingWord]
        dsimp [explicit_length]
        rw [if_pos h]
      · rw [CoxeterSystem.length_alternatingWord]
        dsimp [explicit_length]
        rw [if_neg h]
  rw [h_len_eq] at h_le
  exact (le_antisymm h_le (cs_length_ge_explicit g)).trans h_len_eq.symm

lemma alternating_length (h : i ≠ j) :
    (reducedWord (cs.wordProd (alternatingWord i j n))).length = n := by
  rw [alternating_reducedWord i j n h]
  simp only [length_alternatingWord]

lemma length_eq' (h : i ≠ j) : cs.length (cs.wordProd (alternatingWord i j n)) = n :=
  length_eq (cs.wordProd (CoxeterSystem.alternatingWord i j n)) ▸
    alternating_length h

theorem length_sr_abs (k : ZMod 0) : ℓ (sr k) = (2 * (k.cast : ℤ) - 1).natAbs := by
  rw [length_eq]
  dsimp [reducedWord]
  split_ifs with hk <;> rw [length_alternatingWord] <;> omega

lemma alternatingWord_head_odd (i j : Fin 2) (k : ℕ) :
    (alternatingWord i j (2 * k + 1)).head? = some j := by
  rw [show 2 * k + 1 = (2 * k) + 1 by omega, alternatingWord_succ']
  simp

lemma alternatingWord_head_even_pos (i j : Fin 2) (k : ℕ) (hk : k > 0) :
    (alternatingWord i j (2 * k)).head? = some i := by
  cases k with
  | zero => omega
  | succ k =>
    rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega, alternatingWord_succ']
    simp

@[simp] lemma alternatingWord_getLast_succ (i j : Fin 2) (n : ℕ) :
    (alternatingWord i j (n + 1)).getLast? = some j := by
  rw [alternatingWord_succ]
  simp

lemma alternatingWord_getLast_pos (i j : Fin 2) (n : ℕ) (hn : n > 0) :
    (alternatingWord i j n).getLast? = some j := by
  cases n with
  | zero => omega
  | succ m =>
    exact alternatingWord_getLast_succ i j m

theorem dihedral_induction {P : D∞ → Prop}
    (h1 : P 1)
    (h_s0 : ∀ g, P g → P (g * s0))
    (h_s1 : ∀ g, P g → P (g * s1)) :
    ∀ g, P g := by
  intro g
  rw [← reducedWord_correct g]
  generalize reducedWord g = L
  induction L using List.reverseRecOn with
  | nil =>
    simp only [cs.wordProd_nil]
    exact h1
  | append_singleton xs i ih =>
    -- Inductive step: cs.wordProd (xs ++ [i]) = cs.wordProd xs * s i
    simp only [cs.wordProd_append, cs.wordProd_singleton]
    fin_cases i
    · -- i = 0
      simp only [Fin.zero_eta, Fin.isValue, ← s0']
      apply h_s0
      exact ih
    · -- i = 1
      simp only [Fin.mk_one, Fin.isValue, ← s1']
      apply h_s1
      exact ih

theorem induction_on_alternating {P : D∞ → Prop}
    (h1 : P 1)
    (h_step : ∀ (g : D∞) (s : Fin 2), P g → P (g * cs.simple s)) :
    ∀ g, P g := by
  apply dihedral_induction h1
  · intro g hg; exact h_step g 0 hg
  · intro g hg; exact h_step g 1 hg

-- Alternating cases for D∞
theorem alternating_cases {P : D∞ → Prop}
    (h : ∀ (i j : Fin 2) (n : ℕ), i ≠ j → P (cs.wordProd (alternatingWord i j n))) :
    ∀ g, P g := by
  intro g
  rw [← reducedWord_correct g]
  dsimp [reducedWord]
  cases g with
  | r k =>
    simp only [ge_iff_le, Fin.isValue]
    split_ifs
    · apply h 0 1; decide
    · apply h 1 0; decide
  | sr k =>
    simp only [gt_iff_lt, Fin.isValue]
    split_ifs
    · apply h 0 1; decide
    · apply h 1 0; decide

lemma n_mod_2_induction {P : ℕ → Prop}
  (h0 : ∀ k : ℕ, P (2 * k))
  (h1 : ∀ k : ℕ, P (2 * k + 1)) :
  ∀ n : ℕ, P n := by
  intro n
  rcases Nat.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · rw [← two_mul]
    exact h0 k
  · exact h1 k

lemma length_wordprod {s s' : Fin 2} (n : ℕ) (h_ne : s ≠ s') :
    cs.length (cs.wordProd (alternatingWord s s' n)) = n := by
  rw [length_eq, alternating_length h_ne]
