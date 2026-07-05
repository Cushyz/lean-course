import Dihedral.ReducedWord

open DihedralGroup CoxeterSystem

/-!
Local staging area for lemmas that may eventually be upstreamed to mathlib.

Candidate topics include rank-two alternating words, infinite dihedral length
formulae, and descent lemmas.
-/

lemma zmod0_natAbs_neg_natCast (a : ℕ) :
    Int.natAbs (((-(a : ℤ) : ZMod 0).cast : ℤ)) = a := by
  simp

lemma zmod0_natCast_cast (a : ℕ) : (((a : ZMod 0).cast : ℤ) = (a : ℤ)) := by
  rw [← zmod0_intCast_cast (a : ℤ)]
  rfl

lemma zmod0_neg_natCast_cast (a : ℕ) :
    (((-(a : ℤ) : ZMod 0).cast : ℤ) = -(a : ℤ)) := by
  rw [← zmod0_intCast_cast (-(a : ℤ))]
  rfl

lemma zmod0_natCast_add_one_cast (a : ℕ) :
    ((((a : ℤ) + 1 : ℤ) : ZMod 0).cast : ℤ) = (a : ℤ) + 1 := by
  norm_num

lemma natAbs_two_mul_nat_add_one (a : ℕ) :
    (2 * ((a : ℤ) + 1) - 1).natAbs = 2 * a + 1 := by
  apply Nat.cast_injective (R := ℤ)
  rw [Int.natAbs_of_nonneg (by omega), Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  omega

lemma natAbs_sub_one_of_pos {k : ℤ} (hk : 0 < k) :
    (k - 1).natAbs = k.natAbs - 1 := by
  apply Nat.cast_injective (R := ℤ)
  conv_lhs => rw [Int.natCast_natAbs]
  rw [abs_of_nonneg (by omega : 0 ≤ k - 1)]
  rw [Nat.cast_sub (by omega : 1 ≤ k.natAbs)]
  rw [Int.natCast_natAbs, abs_of_nonneg (by omega : 0 ≤ k)]
  omega

lemma natAbs_sub_one_of_nonpos {k : ℤ} (hk : ¬0 < k) :
    (k - 1).natAbs = k.natAbs + 1 := by
  apply Nat.cast_injective (R := ℤ)
  conv_lhs => rw [Int.natCast_natAbs]
  rw [abs_of_nonpos (by omega : k - 1 ≤ 0)]
  rw [Nat.cast_add, Int.natCast_natAbs, abs_of_nonpos (by omega : k ≤ 0)]
  omega

lemma natAbs_sub_one_le_self_of_pos {k : ℤ} (hk : 0 < k) :
    (k - 1).natAbs ≤ k.natAbs := by
  rw [natAbs_sub_one_of_pos hk]
  exact Nat.sub_le _ _

lemma natAbs_le_natAbs_sub_one_of_nonpos {k : ℤ} (hk : k ≤ 0) :
    k.natAbs ≤ (k - 1).natAbs := by
  rw [natAbs_sub_one_of_nonpos (by omega)]
  omega

lemma natAbs_add_one_le_self_of_neg {k : ℤ} (hk : k < 0) :
    (1 + k).natAbs ≤ k.natAbs := by
  rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs, Int.natCast_natAbs,
    abs_of_nonpos (by omega : 1 + k ≤ 0), abs_of_nonpos (by omega : k ≤ 0)]
  omega

lemma natAbs_one_add_sub_one (k : ℤ) :
    ((1 + k) - 1).natAbs = k.natAbs := by
  ring_nf

lemma two_mul_add_one_div_two (n : ℕ) : (2 * n + 1) / 2 = n := by
  omega

lemma natAbs_add_eq_natAbs_add_two_mul (x y : ℤ) :
    ∃ r : ℕ, x.natAbs + y.natAbs = (x + y).natAbs + 2 * r := by
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · use 0
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero,
        mul_zero, add_zero]
      simp only [Int.natCast_natAbs]
      rw [abs_of_nonneg hx, abs_of_nonneg hy, abs_of_nonneg (by omega : 0 ≤ x + y)]
    · have hy_nonpos : y ≤ 0 := by omega
      by_cases hxy : 0 ≤ x + y
      · use y.natAbs
        apply Nat.cast_injective (R := ℤ)
        rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        simp only [Int.natCast_natAbs]
        rw [abs_of_nonneg hx, abs_of_nonpos hy_nonpos, abs_of_nonneg hxy]
        omega
      · use x.natAbs
        apply Nat.cast_injective (R := ℤ)
        rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        simp only [Int.natCast_natAbs]
        rw [abs_of_nonneg hx, abs_of_nonpos hy_nonpos, abs_of_nonpos (by omega : x + y ≤ 0)]
        omega
  · have hx_nonpos : x ≤ 0 := by omega
    by_cases hy : 0 ≤ y
    · by_cases hxy : 0 ≤ x + y
      · use x.natAbs
        apply Nat.cast_injective (R := ℤ)
        rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        simp only [Int.natCast_natAbs]
        rw [abs_of_nonpos hx_nonpos, abs_of_nonneg hy, abs_of_nonneg hxy]
        omega
      · use y.natAbs
        apply Nat.cast_injective (R := ℤ)
        rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
        simp only [Int.natCast_natAbs]
        rw [abs_of_nonpos hx_nonpos, abs_of_nonneg hy,
          abs_of_nonpos (by omega : x + y ≤ 0)]
        omega
    · have hy_nonpos : y ≤ 0 := by omega
      use 0
      apply Nat.cast_injective (R := ℤ)
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero,
        mul_zero, add_zero]
      simp only [Int.natCast_natAbs]
      rw [abs_of_nonpos hx_nonpos, abs_of_nonpos hy_nonpos,
        abs_of_nonpos (by omega : x + y ≤ 0)]
      omega

lemma natAbs_sub_eq_natAbs_add_two_mul (x y : ℤ) :
    ∃ r : ℕ, x.natAbs + y.natAbs = (x - y).natAbs + 2 * r := by
  simpa [sub_eq_add_neg, Int.natAbs_neg] using natAbs_add_eq_natAbs_add_two_mul x (-y)

lemma infinite_dihedral_closure_simple_reflections :
    (Subgroup.closure ({sr (0 : ZMod 0), sr (1 : ZMod 0)} : Set (DihedralGroup 0))) = ⊤ :=
  gen_by_sr0_sr1

lemma infinite_dihedral_length_reflection_abs (k : ℤ) :
    cs.length (sr k) = (2 * k - 1).natAbs :=
  length_sr_abs k

lemma rank_two_alternatingWord_wordProd_length {s s' : Fin 2} (n : ℕ) (h_ne : s ≠ s') :
    cs.length (cs.wordProd (alternatingWord s s' n)) = n :=
  length_wordprod n h_ne
