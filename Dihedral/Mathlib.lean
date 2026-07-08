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
  omega

lemma natAbs_sub_one_of_pos {k : ℤ} (hk : 0 < k) :
    (k - 1).natAbs = k.natAbs - 1 := by
  omega

lemma natAbs_sub_one_of_nonpos {k : ℤ} (hk : ¬0 < k) :
    (k - 1).natAbs = k.natAbs + 1 := by
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
  omega

lemma natAbs_one_add_sub_one (k : ℤ) :
    ((1 + k) - 1).natAbs = k.natAbs := by
  omega

lemma two_mul_add_one_div_two (n : ℕ) : (2 * n + 1) / 2 = n := by
  omega

lemma natAbs_add_eq_natAbs_add_two_mul (x y : ℤ) :
    ∃ r : ℕ, x.natAbs + y.natAbs = (x + y).natAbs + 2 * r := by
  exact ⟨(x.natAbs + y.natAbs - (x + y).natAbs) / 2, by omega⟩

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
