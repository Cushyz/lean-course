import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Lemmas
import Dihedral.Chain

open CoxeterSystem DihedralGroup Nat

private lemma sr_length_abs_lt_pos_candidate {n p : ZMod 0} {a : ℕ}
    (hp : (p.cast : ℤ) = (a : ℤ) + 1)
    (hleft : ((n.cast : ℤ) - 1).natAbs ≤ a) (hne : n ≠ p) :
    (2 * (n.cast : ℤ) - 1).natAbs < (2 * (p.cast : ℤ) - 1).natAbs := by
  rw [hp, natAbs_two_mul_nat_add_one]
  have hn_cast_ne : (n.cast : ℤ) ≠ (a : ℤ) + 1 := by
    intro hc
    apply hne
    have hnp : (((n.cast : ℤ) : ZMod 0) = ((p.cast : ℤ) : ZMod 0)) := by
      simp [hc, hp]
    exact (ZMod.intCast_zmod_cast n).symm.trans (hnp.trans (ZMod.intCast_zmod_cast p))
  omega

private lemma sr_length_abs_lt_neg_candidate {n p : ZMod 0} {b : ℕ}
    (hp : (p.cast : ℤ) = -(b : ℤ))
    (hright : (n.cast : ℤ).natAbs ≤ b) (hne : n ≠ p) :
    (2 * (n.cast : ℤ) - 1).natAbs < (2 * (p.cast : ℤ) - 1).natAbs := by
  have hn_cast_ne : (n.cast : ℤ) ≠ -(b : ℤ) := by
    intro hc
    apply hne
    have hnp : (((n.cast : ℤ) : ZMod 0) = ((p.cast : ℤ) : ZMod 0)) := by
      simp [hc, hp]
    exact (ZMod.intCast_zmod_cast n).symm.trans (hnp.trans (ZMod.intCast_zmod_cast p))
  rw [hp]
  omega

-- (Reachable Set)
def ReachableSet (u : Vertex) (d : Degree) : Set Vertex :=
  { v | ∃ d', HasChain u v d' ∧ d' ≤ d }

def IsMaximalIn (v : Vertex) (S : Set Vertex) : Prop :=
  v ∈ S ∧ ∀ v' ∈ S, v ≤ v' → v = v'

-- 定义 CurveNeighborhood
def CurveNeighborhood (u : Vertex) (d : Degree) : Set Vertex :=
  { v | IsMaximalIn v (ReachableSet u d) }

-- 定义集合 A_d(u)
def Ad (u : Vertex) (d : Degree) : Set Vertex :=
  { v |  ℓ (u * v) = ℓ u +  ℓ v ∧ φ v ≤ d }

-- 定义集合 S 中的极大元子集
def maximalElements (S : Set Vertex) : Set Vertex :=
  { v | IsMaximalIn v S }

private lemma sr_additive_same_abs_eq {nu nx ny : ℤ}
    (hw : (if 0 < nu + ny then 2 * Int.natAbs (nu + ny) - 1
        else 2 * Int.natAbs (nu + ny) + 1) =
      (if 0 < nu then 2 * nu.natAbs - 1 else 2 * nu.natAbs + 1) + 2 * ny.natAbs)
    (hv : (if 0 < nu + nx then 2 * Int.natAbs (nu + nx) - 1
        else 2 * Int.natAbs (nu + nx) + 1) =
      (if 0 < nu then 2 * nu.natAbs - 1 else 2 * nu.natAbs + 1) + 2 * ny.natAbs)
    (h_abs : nx.natAbs = ny.natAbs) :
    nx = ny := by
  have hvw := hv.trans hw.symm
  split_ifs at hvw <;> omega

private lemma sr_reflection_additive_same_odd_abs_eq {nu nx ny : ℤ}
    (hw : 2 * Int.natAbs (ny - nu) =
      (2 * nu - 1).natAbs + (2 * ny - 1).natAbs)
    (hv : 2 * Int.natAbs (nx - nu) =
      (2 * nu - 1).natAbs + (2 * nx - 1).natAbs)
    (h_abs : (2 * nx - 1).natAbs = (2 * ny - 1).natAbs) :
    nx = ny := by
  omega

private lemma r_additive_same_abs_eq {nu nx ny : ℤ}
    (hnu : nu ≠ 0)
    (hw : 2 * Int.natAbs (nu + ny) = 2 * nu.natAbs + 2 * ny.natAbs)
    (hv : 2 * Int.natAbs (nu + nx) = 2 * nu.natAbs + 2 * nx.natAbs)
    (h_abs : nx.natAbs = ny.natAbs) :
    nx = ny := by
  omega

private lemma r_reflection_additive_same_odd_abs_eq {nu nx ny : ℤ}
    (hnu : nu ≠ 0)
    (hw : (2 * (ny - nu) - 1).natAbs =
      2 * nu.natAbs + (2 * ny - 1).natAbs)
    (hv : (2 * (nx - nu) - 1).natAbs =
      2 * nu.natAbs + (2 * nx - 1).natAbs)
    (h_abs : (2 * nx - 1).natAbs = (2 * ny - 1).natAbs) :
    nx = ny := by
  omega

--欲证明有限集
lemma h_len_bound : ∀ v ∈ Ad u d, ℓ v ≤ d.a + d.b + 1 := by
    intro v hv
    obtain ⟨h, h_deg⟩ := hv
    induction v using alternating_cases with
    | h s s' n h2=>
      simp_all only [ne_eq, length_wordprod n h2, Degreele_le_def]
      induction n using n_mod_2_induction with
      | h0 k =>
        rw [show s'=1 - s by omega, getDegree_alternatin_even k] at *
        linarith
      | h1 k =>
        fin_cases s <;>simp_all
        · erw [show s' =1 by omega, getDegree_alternating_0_odd] at h_deg
          linarith
        · erw [show s' =0 by omega, getDegree_alternating_1_odd] at h_deg
          linarith

lemma h_finite : (Ad u d).Finite := by
    let limit := d.a + d.b + 1
    let S_bound := {v : D∞ | ℓ v ≤ limit}
    have h_subset : Ad u d ⊆ S_bound := fun v hv => h_len_bound v hv
    apply Set.Finite.subset _ h_subset
    have : S_bound = ⋃ k ∈ Finset.range (limit + 1), {v | ℓ v = k} := by
      ext x
      simp only [S_bound, Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_range]
      constructor
      · intro h; use ℓ x; constructor <;> linarith
      · rintro ⟨i, hi, hx⟩; rw [hx]; linarith
    rw [this]
    have hfinite :
        (⋃ k ∈ (Finset.range (limit + 1) : Set ℕ),
          {v | ℓ v = k}).Finite := by
      apply Set.Finite.biUnion (Finset.finite_toSet _)
      intro k hk
      have h_finite_image : (Set.range (fun (s : Fin 2) =>
        cs.wordProd (alternatingWord s (1-s) k))).Finite := Set.finite_range _
      apply Set.Finite.subset h_finite_image
      intro v hv
      simp only [Set.mem_setOf_eq] at hv
      revert hv
      apply alternating_cases (P := fun v => ℓ v = k →
         v ∈ Set.range fun s => cs.wordProd (alternatingWord s (1-s) k))
      intro s1 s2 n h_ne h_len
      rw [length_wordprod n h_ne] at h_len
      subst h_len
      have hs2 : s2 = 1 - s1 := by
        fin_cases s1 <;> fin_cases s2 <;> simp at h_ne ⊢
      subst s2
      exact Set.mem_range_self s1
    simpa using hfinite

lemma ad_finite : (Ad u d).Finite :=
  h_finite

lemma h_nonempty : (Ad u d).Nonempty := ⟨1, ⟨by simp, by
    simp [getDegree_one]⟩⟩

lemma ad_nonempty : (Ad u d).Nonempty :=
  h_nonempty

lemma h_chain {u : Vertex} (h : u ≠ 1) : IsChain (· ≤ ·) (Ad u d) := by
  intro x hx y hy hxy
  suffices h : (x < y) ∨ (y < x) by
    rcases h with h | h
    · left; exact le_of_lt h
    · right; exact le_of_lt h
  rcases hx with ⟨hv, hv'⟩
  rcases hy with ⟨hw, hw'⟩
  rcases d with ⟨a,b⟩
  simp_all only [ne_eq, Degreele_le_def, lt_iff_length_lt, lt_or_lt_iff_ne]
  cases u with
  | sr nu =>
    rcases x with ⟨nx⟩ | ⟨nx⟩ <;>
    rcases y with ⟨ny⟩ | ⟨ny⟩
    · simp_all only [sr_mul_r, length_sr, length_r, r.injEq, mul_eq_mul_left_iff,
        OfNat.ofNat_ne_zero, or_false]
      intro h_abs
      rw [h_abs] at hv
      change ℤ at *
      exact hxy (sr_additive_same_abs_eq hw hv h_abs)
    · rw [length_r, length_sr_abs]; omega
    · rw [length_r, length_sr_abs]; omega
    · simp only [sr_mul_sr] at hv hw
      rw [length_sr_abs, length_sr_abs, length_r] at hv hw
      rw [length_sr_abs, length_sr_abs]
      simp_all only [getDegree_sr, sr.injEq]
      change ℤ at *
      intro h_abs
      exact hxy (sr_reflection_additive_same_odd_abs_eq
        (nu := nu) (nx := nx) (ny := ny) hw hv h_abs)
  | r nu =>
    have nun0 : nu ≠ 0 := by
      intro p
      simp [p] at h
    rcases x with ⟨nx⟩ | ⟨nx⟩ <;>
    rcases y with ⟨ny⟩ | ⟨ny⟩
    · simp_all only [ne_eq, getDegree_r, r_mul_r, length_r, r.injEq, mul_eq_mul_left_iff,
      OfNat.ofNat_ne_zero, or_false]
      change ℤ at *
      intro h_abs
      exact hxy (r_additive_same_abs_eq nun0 hw hv h_abs)
    · rw [length_r, length_sr_abs]; omega
    · rw [length_r, length_sr_abs]; omega
    · simp only [r_mul_sr] at hv hw
      rw [length_sr_abs, length_sr_abs, length_r] at hv hw
      rw [length_sr_abs, length_sr_abs]
      simp_all only [ne_eq, getDegree_sr, sr.injEq]
      change ℤ at *
      intro h_abs
      exact hxy (r_reflection_additive_same_odd_abs_eq
        (nu := nu) (nx := nx) (ny := ny) nun0 hw hv h_abs)

lemma ad_isChain_of_ne_one {u : Vertex} (h : u ≠ 1) : IsChain (· ≤ ·) (Ad u d) :=
  h_chain h

lemma ad_length_bound : ∀ v ∈ Ad u d, ℓ v ≤ d.a + d.b + 1 :=
  h_len_bound

theorem exists_unique_max_ad_ne_one (u : Vertex) (d : Degree) :
    (u ≠ 1) → ∃! v, IsMaximalIn v (Ad u d) := by
  intro h_cond
  obtain ⟨m, hm⟩ := Set.Finite.exists_maximalFor (fun x => x) (Ad u d) ad_finite ad_nonempty
  refine ⟨m, ?_⟩
  dsimp [IsMaximalIn]
  constructor
  · constructor
    · exact hm.1
    · intro v' hv' h_le
      have := by apply hm.2  hv'  h_le
      exact le_antisymm h_le this
  · rintro y ⟨hy_in, hy_max⟩
    have h_total : m ≤ y ∨ y ≤ m := by
      by_cases eq : m = y
      · left; rw [eq]
      · apply ad_isChain_of_ne_one h_cond hm.1 hy_in eq
    cases h_total with
    | inl h_le =>
      symm
      have := hm.2 hy_in h_le
      exact le_antisymm h_le this
    | inr h_le =>
      apply hy_max m hm.1 h_le

lemma ad_one_eq_degree_le (d : Degree) : Ad 1 d = {x : Vertex | φ x ≤ d} := by
  simp [Ad, one_mul]

theorem exists_unique_max_ad_one_neq (d : Degree) :
     (d.a ≠ d.b) → ∃! v, IsMaximalIn v (Ad 1 d) := by
      intro ne
      rcases d with ⟨a, b⟩
      dsimp [IsMaximalIn]
      rw [Nat.ne_iff_lt_or_gt] at ne
      simp only [ad_one_eq_degree_le]
      rcases ne with h | h
      · -- a < b. v = sr (-(b)). a = b or a < b.
        -- But root ⟨b+1, b⟩ => s_alpha = sr (-b)
        use s_α ⟨a, a + 1, Or.inr rfl⟩ -- Wait, if a < b, maximal is in terms of b?
        -- If a < b, maximal element is sr (a+1) (k>0) or sr (-b) (k<=0)?
        -- Let's check degrees.
        -- φ (sr k) = (|k-1|, |k|) if k>0; (|k|+1, |k|) if k<=0.
        -- We want (x, y) <= (a, b).
        -- If k > 0: |k-1| <= a, |k| <= b.
        -- Max possible k: |k| <= b. If k=b, |b-1| = b-1. If b-1 <= a?
        -- Given a < b. b-1 could be a.
        -- If k <= 0: |k|+1 <= a, |k| <= b. |k| <= a-1.
        -- Max length ~ 2*deg.
        -- Let's stick to the structure.
        -- If a < b, max element is s_alpha_d corresponding to a
        -- actually s_alpha_d is defined by comparing a and b.
        -- If a < b, root is <a, a+1> -> sr (a+1).
        -- Check degree sr (a+1): <a, a+1>. fits if a+1 <= b.
        -- Yes, a < b => a+1 <= b.
        -- So v = sr (a+1).
        --use s_α ⟨a, a + 1, Or.inr rfl⟩
        simp only at h
        have h': a + 1 ≤ b := by omega
        simp only [Degreele_le_def, s_α, gt_iff_lt, add_lt_iff_neg_left, _root_.not_lt_zero,
          ↓reduceIte, Fin.isValue, show a + (a + 1) = 2 * a + 1 by omega, Set.mem_setOf_eq,
          getDegree_alternating_0_odd a, le_refl, h', and_self, and_imp, true_and]
        -- s_α uses wordProd alternatingWord.
        -- For <a, a+1>, it's alternatingWord 0 1 (2a+1).
        rw [cs.prod_alternatingWord_eq_mul_pow 0 1 (2*a+1)]
        have h_div : (2 * a + 1) / 2 = a := by omega
        simp only [not_even_bit1, ↓reduceIte, Fin.isValue, ← s1', s1, ← s0', s0, sr_mul_sr,
          sub_zero, h_div, r_pow, one_mul, sr_mul_r]
        split_ands
        · intro v h1 h2 h3
          let a' := (a : ℤ)
          have h3 : ( ℓ (sr (1 + a)) < ℓ v) ∨ (sr (1 + a : ℕ) = v) := by
            simp only[← lt_iff_length_lt] ; exact h3
          cases v with
          | r n =>
            rw [length_sr_abs, length_r] at h3
            simp_all [getDegree_r]
            omega
          | sr n =>
            repeat rw [length_sr_abs] at h3
            simp_all only [getDegree_sr, cast_add, cast_one, sr.injEq]
            by_contra hne
            simp [hne] at h3
            let q : ZMod 0 := (1 + (a : ℤ) : ℤ)
            have hq_cast : (q.cast : ℤ) = (a : ℤ) + 1 := by
              dsimp [q]
              rw [show 1 + (a : ℤ) = (a : ℤ) + 1 by omega]
              exact zmod0_natCast_add_one_cast a
            have hnq : n ≠ q := by
              intro hnq
              apply hne
              exact hnq.symm
            have hlt := sr_length_abs_lt_pos_candidate (n := n) (p := q) hq_cast h1 hnq
            have hq_len :
                (2 * (q.cast : ℤ) - 1).natAbs =
                  (2 * (1 + (a : ℤ)) - 1).natAbs := by
              apply congrArg Int.natAbs
              rw [hq_cast]
              omega
            rw [hq_len] at hlt
            exact (not_lt_of_gt hlt h3)
        · intro v h1 h2 h3
          let p : ZMod 0 := ((a : ℤ) + 1 : ℤ)
          have hp_cast : (p.cast : ℤ) = (a : ℤ) + 1 := by
            dsimp [p]
            exact zmod0_natCast_add_one_cast a
          have hp_deg_left : ((p.cast : ℤ) - 1).natAbs ≤ a := by
            rw [hp_cast]
            simp
          have hp_deg_right : (p.cast : ℤ).natAbs ≤ b := by
            rw [hp_cast]
            exact_mod_cast h'
          cases v with
          | r n =>
            simp_all only [getDegree_r, reduceCtorEq]
            specialize h3 (sr p)
            simp_all only [getDegree_sr, add_sub_cancel_right, Int.natAbs_natCast, le_refl,
              reduceCtorEq, imp_false, forall_const]
            have hlt : ℓ (r n) < ℓ (sr p) := by
              rw [length_r, length_sr_abs]
              rw [hp_cast, natAbs_two_mul_nat_add_one]
              exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 h1) (by omega)
            exact h3 (le_of_lt ((lt_iff_length_lt _ _).mpr hlt))
          | sr n =>
            specialize h3 (sr p)
            simp_all only [getDegree_sr, add_sub_cancel_right, Int.natAbs_natCast, le_refl,
              sr.injEq, forall_const]
            rw [add_comm]
            by_cases hn : n = p
            · exact hn
            have hlt : ℓ (sr n) < ℓ (sr p) := by
              rw [length_sr_abs, length_sr_abs]
              exact sr_length_abs_lt_pos_candidate hp_cast h1 hn
            exact h3 (le_of_lt ((lt_iff_length_lt _ _).mpr hlt))
      · -- a > b. v = sr (-b).
        use s_α ⟨b + 1, b, Or.inl rfl⟩
        simp only at h
        have h' : b + 1 ≤ a := by linarith
        simp only [Degreele_le_def, s_α, gt_iff_lt, lt_add_iff_pos_right, zero_lt_one, ↓reduceIte,
          Fin.isValue, show b + 1 + b = 2 * b + 1 by omega, Set.mem_setOf_eq,
          getDegree_alternating_1_odd b, h', le_refl, and_self, and_imp, true_and]
        rw [cs.prod_alternatingWord_eq_mul_pow 1 0 (2*b+1)]
        have h_div : (2 * b + 1) / 2 = b := by omega
        simp only [not_even_bit1, ↓reduceIte, Fin.isValue, ← s0', s0, ← s1', s1, sr_mul_sr,
          zero_sub, h_div, r_pow, neg_mul, one_mul, sr_mul_r, zero_add]
        split_ands
        · intro v h1 h2 h3
          have h3 : ( ℓ (sr (-(b:ℤ))) < ℓ v) ∨ (sr (-(b:ℤ)) = v) := by
            rw [← lt_iff_length_lt] ; exact h3
          cases v with
          | r n =>
            rw [length_sr_abs, length_r] at h3
            simp_all [getDegree_r]
            omega
          | sr n =>
            repeat rw [length_sr_abs] at h3
            simp_all only [getDegree_sr, sr.injEq]
            by_contra hne
            simp at h3
            let q : ZMod 0 := (-(b : ℤ) : ℤ)
            have hq_cast : (q.cast : ℤ) = -(b : ℤ) := by
              dsimp [q]
              exact zmod0_neg_natCast_cast b
            have hnq : n ≠ q := by
              intro hnq
              apply hne
              exact hnq.symm
            have hlt := sr_length_abs_lt_neg_candidate (n := n) (p := q) hq_cast h2 hnq
            have hq_len :
                (2 * (q.cast : ℤ) - 1).natAbs =
                  (2 * (-(b : ℤ)) - 1).natAbs := by
              apply congrArg Int.natAbs
              rw [hq_cast]
            rw [hq_len] at hlt
            rcases h3 with h3 | heq
            · have h3' :
                  (2 * (-(b : ℤ)) - 1).natAbs < (2 * (n.cast : ℤ) - 1).natAbs := by
                simpa using h3
              exact (not_lt_of_gt hlt h3')
            · exact hne heq
        · intro v h1 h2 h3
          let p : ZMod 0 := (-(b : ℤ) : ℤ)
          have hp_cast : (p.cast : ℤ) = -(b : ℤ) := by
            dsimp [p]
            exact zmod0_neg_natCast_cast b
          have hp_deg_left : ((p.cast : ℤ) - 1).natAbs ≤ a := by
            rw [hp_cast]
            have : (b : ℤ) + 1 ≤ (a : ℤ) := by exact_mod_cast h'
            omega
          have hp_deg_right : (p.cast : ℤ).natAbs ≤ b := by
            rw [hp_cast]
            simp
          cases v with
          | r n =>
            simp_all only [getDegree_r, reduceCtorEq]
            specialize h3 (sr p)
            simp_all only [getDegree_sr, Int.natAbs_neg, Int.natAbs_natCast, le_refl, reduceCtorEq,
              imp_false, forall_const]
            have hlt : ℓ (r n) < ℓ (sr p) := by
              rw [length_r, length_sr_abs]
              have hp_len : (2 * (p.cast : ℤ) - 1).natAbs = 2 * b + 1 := by
                rw [hp_cast]; omega
              rw [hp_len]
              exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left 2 h2) (by omega)
            exact h3 (le_of_lt ((lt_iff_length_lt _ _).mpr hlt))
          | sr n =>
            specialize h3 (sr p)
            simp_all only [getDegree_sr, Int.natAbs_neg, Int.natAbs_natCast, le_refl, sr.injEq,
              forall_const]
            by_cases hn : n = p
            · exact hn
            have hlt : ℓ (sr n) < ℓ (sr p) := by
              rw [length_sr_abs, length_sr_abs]
              exact sr_length_abs_lt_neg_candidate hp_cast h2 hn
            exact h3 (le_of_lt ((lt_iff_length_lt _ _).mpr hlt))

theorem max_ad_one_diag_iff_r_or_neg_r (a : ℕ) (v : Vertex) :
    let S := Ad 1 (Degree.mk a a)
    IsMaximalIn v S ↔ v = r (a : ℤ) ∨ v = r (-(a : ℤ)) := by
  simp only [ad_one_eq_degree_le, Degreele_le_def]
  have h_len_le : ∀ x, getDegree x ≤ Degree.mk a a → ℓ x ≤ 2 * a := by
    intro x h_deg
    rcases x with (_ | k)
    · simp only [getDegree_r, Degreele_le_def] at h_deg
      rw [length_r]
      exact Nat.mul_le_mul_left 2 h_deg.1
    · simp only [getDegree_sr, Degreele_le_def] at h_deg
      rw [length_sr]
      split_ifs with h_pos
      · by_cases hk0 : k = 0
        · simp [hk0] at h_deg ⊢
        · exact le_trans (Nat.sub_le _ _) (Nat.mul_le_mul_left 2 h_deg.2)
      · have hk_nonpos : (k.cast : ℤ) ≤ 0 := le_of_not_gt h_pos
        have h_abs_sub : ((k.cast : ℤ) - 1).natAbs = (k.cast : ℤ).natAbs + 1 := by
          omega
        rw [h_abs_sub] at h_deg
        have hmul : 2 * ((k.cast : ℤ).natAbs + 1) ≤ 2 * a :=
          Nat.mul_le_mul_left 2 h_deg.1
        have hstep : 2 * (k.cast : ℤ).natAbs + 1 ≤ 2 * ((k.cast : ℤ).natAbs + 1) := by
          omega
        exact le_trans hstep hmul
  -- r a, r (-a) ∈ S
  have h_mem_pos : getDegree (r (a : ℤ)) ≤ Degree.mk a a := by
    simp [getDegree_r]
  have h_mem_neg : getDegree (r (-(a : ℤ))) ≤ Degree.mk a a := by
    simp [getDegree_r]
  have h_maximal_iff_len : IsMaximalIn v {x | getDegree x ≤ Degree.mk a a} ↔
                           getDegree v ≤ Degree.mk a a ∧ ℓ v = 2 * a := by
    constructor
    · rintro ⟨h_in, h_max⟩
      constructor
      · exact h_in
      · by_contra h_len_ne
        have h_len_lt : ℓ v < 2 * a := lt_of_le_of_ne (h_len_le v h_in) h_len_ne
        let w := r (a : ZMod 0)
        have h_w_in : w ∈ {x | getDegree x ≤ Degree.mk a a} := h_mem_pos
        have h_len_w : ℓ w = 2 * a := by simp [w, length_r]; omega
        have h_lt : v < w := (lt_iff_length_lt v w).mpr (by rw [h_len_w]; exact h_len_lt)
        have h_le : v ≤ w := le_of_lt h_lt
        have h_eq := h_max w h_w_in h_le
        rw [h_eq] at h_len_lt
        rw [h_len_w] at h_len_lt
        exact lt_irrefl _ h_len_lt
    · rintro ⟨h_in, h_len_eq⟩
      constructor
      · exact h_in
      · intro v' h_in' h_le
        rcases h_le with h_lt | h_eq
        · have h_len_lt : ℓ v < ℓ v' := (lt_iff_length_lt v v').mp h_lt
          rw [h_len_eq] at h_len_lt
          have h_bound := h_len_le v' h_in'
          linarith
        · exact h_eq
  have h_set_eq : {x | getDegree x ≤ { a := a, b := a }} =
     {x | (getDegree x).a ≤ a ∧ (getDegree x).b ≤ a} := by
    ext x;simp only [Degreele_le_def, Set.mem_setOf_eq]
  rw [← h_set_eq, h_maximal_iff_len]
  constructor
  · rintro ⟨h_deg, h_len⟩
    cases v with
    | r k =>
      simp [length_r] at h_len
      have hk : k.natAbs = a := by linarith
      rw [Int.natAbs_eq_iff] at hk
      rcases hk with rfl | rfl
      · left; rfl
      · right; rfl
    | sr k =>
      simp [length_sr] at h_len
      split_ifs at h_len
      <;> omega
  · rintro (rfl | rfl)
    · exact ⟨h_mem_pos, by simp [length_r]⟩
    · exact ⟨h_mem_neg, by simp [length_r]⟩

