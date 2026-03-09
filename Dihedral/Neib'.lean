import Mathlib
import Dihedral.alternatingword
import Dihedral.Degree'

open CoxeterSystem DihedralGroup Nat

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

lemma h_nonempty : (Ad u d).Nonempty := ⟨1, ⟨by simp, by
    simp [getDegree_one]⟩⟩

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
    · simp_all; grind
    · simp_all; grind
    · simp_all; grind
    · simp only [sr_mul_sr] at hv hw
      rw [length_sr_abs, length_sr_abs, length_r] at hv hw
      rw [length_sr_abs, length_sr_abs]
      simp_all only [getDegree_sr, sr.injEq]
      change ℤ at *
      have : nx < ny ∨ ny < nx := Int.ne_iff_lt_or_gt.mp hxy
      omega
  | r nu =>
    have nun0 : nu ≠ 0 := by
      intro p
      simp [p] at h
    rcases x with ⟨nx⟩ | ⟨nx⟩ <;>
    rcases y with ⟨ny⟩ | ⟨ny⟩
    · simp_all only [ne_eq, getDegree_r, r_mul_r, length_r, r.injEq, mul_eq_mul_left_iff,
      OfNat.ofNat_ne_zero, or_false]
      change ℤ at *
      grind
    · simp_all; grind
    · simp_all; grind
    · simp only [r_mul_sr] at hv hw
      rw [length_sr_abs, length_sr_abs, length_r] at hv hw
      rw [length_sr_abs, length_sr_abs]
      simp_all only [ne_eq, getDegree_sr, sr.injEq]
      change ℤ at *
      grind

theorem exists_unique_max_ad_ne_one (u : Vertex) (d : Degree) :
    (u ≠ 1) → ∃! v, IsMaximalIn v (Ad u d) := by
  intro h_cond
  obtain ⟨m, hm⟩ := Set.Finite.exists_maximalFor (fun x => x) (Ad u d) h_finite h_nonempty
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
      · apply h_chain h_cond hm.1 hy_in eq
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
            by_contra p
            simp [p] at h3
            omega
        · intro v h1 h2 h3
          cases v with
          | r n =>
            simp_all only [getDegree_r, reduceCtorEq]
            specialize h3 (sr ((a:ℕ)+1:ℤ))
            simp_all only [getDegree_sr, add_sub_cancel_right, Int.natAbs_natCast, le_refl,
              reduceCtorEq, imp_false, forall_const]
            norm_cast at h3
            refine h3 h (le_of_eq_or_lt ?_)
            simp only [cast_add, cast_one, reduceCtorEq, false_or]
            have h: ℓ (r n) < ℓ (sr ((a:ℕ)+1:ℤ)) := by
              rw [length_r,length_sr_abs]; omega
            exact (lt_iff_length_lt _ _).mpr h
          | sr n =>
            specialize h3 (sr ((a:ℕ)+1:ℤ))
            simp_all only [getDegree_sr, add_sub_cancel_right, Int.natAbs_natCast, le_refl,
              sr.injEq, forall_const]
            rw [add_comm]
            apply h3
            · omega
            · apply le_of_eq_or_lt
              rw [lt_iff_length_lt, length_sr_abs,length_sr_abs]
              grind
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
            by_contra p
            simp [p] at h3
            omega
        · intro v h1 h2 h3
          cases v with
          | r n =>
            simp_all only [getDegree_r, reduceCtorEq]
            specialize h3 (sr (-b:ℤ))
            simp_all only [getDegree_sr, Int.natAbs_neg, Int.natAbs_natCast, le_refl, reduceCtorEq,
              imp_false, forall_const]
            norm_cast at h3
            refine h3 (by omega) (le_of_eq_or_lt ?_)
            simp only [reduceCtorEq, false_or]
            have h: ℓ (r n) < ℓ (sr (-b:ℤ)) := by
              rw [length_r,length_sr_abs]; omega
            exact (lt_iff_length_lt _ _).mpr h
          | sr n =>
            specialize h3 (sr (-b:ℤ))
            simp_all only [getDegree_sr, Int.natAbs_neg, Int.natAbs_natCast, le_refl, sr.injEq,
              forall_const]
            apply h3
            · omega
            · apply le_of_eq_or_lt
              rw [lt_iff_length_lt, length_sr_abs,length_sr_abs]
              grind

theorem max_ad_one_diag_iff_r_or_neg_r (a : ℕ) (v : Vertex) :
    let S := Ad 1 (Degree.mk a a)
    IsMaximalIn v S ↔ v = r (a : ℤ) ∨ v = r (-(a : ℤ)) := by
  simp only [ad_one_eq_degree_le, Degreele_le_def]
  have h_len_le : ∀ x, getDegree x ≤ Degree.mk a a → ℓ x ≤ 2 * a := by
    intro x h_deg
    rcases x with (_ | k)
    · simp only [getDegree_r, Degreele_le_def] at h_deg
      rw [length_r]
      omega
    · simp only [getDegree_sr, Degreele_le_def] at h_deg
      rw [length_sr]
      split_ifs with h_pos
      · by_cases hk0 : k = 0
        · simp [hk0] at h_deg ⊢
        · omega
      · omega
  -- r a, r (-a) ∈ S
  have h_mem_pos : getDegree (r (a : ℤ)) ≤ Degree.mk a a := by
    simp only [getDegree_r, Int.natAbs_natCast, le_refl]
  have h_mem_neg : getDegree (r (-(a : ℤ))) ≤ Degree.mk a a := by
    simp only [getDegree_r, Int.natAbs_neg, Int.natAbs_natCast, le_refl]
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

def root_from_degree (d : Degree) : Root :=
  if d.a > d.b then
    ⟨d.b + 1, d.b, Or.inl rfl⟩
  else
    ⟨d.a, d.a + 1, Or.inr rfl⟩

def s_alpha_d (d : Degree) : Vertex := s_α (root_from_degree d)

def s0s1_pow (a : ℕ) : Vertex := cs.wordProd (alternatingWord 0 1 (2 * a))
def s1s0_pow (a : ℕ) : Vertex := cs.wordProd (alternatingWord 1 0 (2 * a))

lemma s0s1_pow_equiv (a : ℕ) : s0s1_pow a = r (a : ℤ) := by
  simp only [s0s1_pow, Fin.isValue]
  rw [cs.prod_alternatingWord_eq_mul_pow 0 1]
  simp [s0, s1, sr_mul_sr, ← s0', ← s1']

lemma s1s0_pow_equiv (a : ℕ) : s1s0_pow a = r (-(a : ℤ)) := by
  simp only [s1s0_pow, Fin.isValue]
  rw [cs.prod_alternatingWord_eq_mul_pow 1 0]
  simp [s0, s1, sr_mul_sr, ← s0', ← s1']

lemma phi_sr0_add_phi_sr_eq_phi_r_pos (k : ℤ) (hk : 0 < k) :
    φ (sr (0 : ℤ)) + φ (sr k) = φ (r k) := by
  ext
  · have h_nat : (k - 1).natAbs = k.natAbs - 1 := by omega
    simpa [getDegree_sr, getDegree_r, h_nat, instAddDegree, Add.add] using
      (show 1 + (k.natAbs - 1) = k.natAbs by omega)
  · rw [getDegree_sr, getDegree_sr, getDegree_r]
    have hb0 : (({ a := ((0 : ℤ) - 1).natAbs, b := Int.natAbs (0 : ℤ) } : Degree) +
      ({ a := (k - 1).natAbs, b := k.natAbs } : Degree)).b =
      Int.natAbs (0 : ℤ) + k.natAbs := by rfl
    rw [hb0]
    simp

lemma phi_sr1_add_phi_sr_succ_eq_phi_r_neg (k : ℤ) (hk : k < 0) :
    φ (sr (1 : ℤ)) + φ (sr ((k + 1 : ℤ))) = φ (r k) := by
  have h_abs_step : (k + 1).natAbs + 1 = k.natAbs := by omega
  ext
  · rw [getDegree_sr, getDegree_sr, getDegree_r]
    have hk_id : k + 1 - 1 = k := by ring
    have ha0 : (({ a := ((1 : ℤ) - 1).natAbs, b := Int.natAbs (1 : ℤ) } : Degree) +
      ({ a := (k + 1 - 1).natAbs, b := (k + 1).natAbs } : Degree)).a
      = ((1 : ℤ) - 1).natAbs + (k + 1 - 1).natAbs := by rfl
    rw [ha0]
    simp [hk_id]
  · rw [getDegree_sr, getDegree_sr, getDegree_r]
    have hb0 : (({ a := ((1 : ℤ) - 1).natAbs, b := Int.natAbs (1 : ℤ) } : Degree) +
      ({ a := (k + 1 - 1).natAbs, b := (k + 1).natAbs } : Degree)).b
      = Int.natAbs (1 : ℤ) + (k + 1).natAbs := by rfl
    rw [hb0]
    simp [h_abs_step, Nat.add_comm]

lemma trivial_chain_sr (k : ℤ) : HasChain 1 (sr k) (φ (sr k)) := by
  obtain ⟨α, hα⟩ := exists_root_eq_sr k
  have h_edge : IsEdge 1 (sr k) α := by
    dsimp [IsEdge]
    rw [hα, one_mul]
  have h_deg : α.toDegree = φ (sr k) := by
    rw [← hα]
    simpa using (φ_s_alpha_eq α).symm
  rw [← h_deg]
  simpa using
    (HasChain.step (HasChain.refl 1) h_edge : HasChain 1 (sr k) (0 + α.toDegree))

lemma trivial_chain_r_pos (k : ℤ) (hk : 0 < k) : HasChain 1 (r k) (φ (r k)) := by
  obtain ⟨αk, hαk⟩ := exists_root_eq_sr k
  have h_chain0 : HasChain 1 (sr (0 : ℤ)) (φ (sr (0 : ℤ))) := trivial_chain_sr 0
  have h_edgek : IsEdge (sr (0 : ℤ)) (r k) αk := by
    dsimp [IsEdge]
    rw [hαk, sr_mul_sr, sub_zero]
  have h_chaink : HasChain 1 (r k) (φ (sr (0 : ℤ)) + αk.toDegree) :=
    HasChain.step h_chain0 h_edgek
  have h_degk : αk.toDegree = φ (sr k) := by
    rw [← hαk]
    simpa using (φ_s_alpha_eq αk).symm
  rw [h_degk] at h_chaink
  rw [phi_sr0_add_phi_sr_eq_phi_r_pos k hk] at h_chaink
  exact h_chaink

lemma trivial_chain_r_neg (k : ℤ) (hk : k < 0) : HasChain 1 (r k) (φ (r k)) := by
  obtain ⟨αk1, hαk1⟩ := exists_root_eq_sr (k + 1)
  have h_chain1 : HasChain 1 (sr (1 : ℤ)) (φ (sr (1 : ℤ))) := trivial_chain_sr 1
  have h_edgek1 : IsEdge (sr (1 : ℤ)) (r k) αk1 := by
    dsimp [IsEdge]
    rw [hαk1, sr_mul_sr]
    ring_nf
  have h_chaink1 : HasChain 1 (r k) (φ (sr (1 : ℤ)) + αk1.toDegree) :=
    HasChain.step h_chain1 h_edgek1
  have h_degk1 : αk1.toDegree = φ (sr ((k + 1 : ℤ))) := by
    rw [← hαk1]
    simpa using (φ_s_alpha_eq αk1).symm
  rw [h_degk1] at h_chaink1
  rw [phi_sr1_add_phi_sr_succ_eq_phi_r_neg k hk] at h_chaink1
  exact h_chaink1

lemma trivial_chain (u : Vertex) : HasChain 1 u (φ u) := by
  cases u with
  | sr k =>
    simpa using trivial_chain_sr (k : ℤ)
  | r k =>
    let k' : ℤ := k
    by_cases hk0 : k' = 0
    · subst hk0
      simpa [getDegree_one] using (HasChain.refl (1 : Vertex))
    · by_cases hk_pos : 0 < k'
      · simpa [k'] using trivial_chain_r_pos k' hk_pos
      · have hk_neg : k' < 0 := by omega
        simpa [k'] using trivial_chain_r_neg k' hk_neg

-- 结论 A
theorem curve_nbhd_one_eq_max_ad_one (d : Degree) :
    CurveNeighborhood 1 d = { v | IsMaximalIn v (Ad 1 d) } := by
  rw [CurveNeighborhood]
  congr
  ext v
  constructor
  · rintro h_in_Re
    simp only [ReachableSet] at h_in_Re
    simp only [Ad, one_mul, cs.length_one, zero_add, true_and]
    have h_deg_le : getDegree v ≤ d := by
      rcases h_in_Re with ⟨h_mem, _⟩
      simp only [Set.mem_setOf_eq] at h_mem
      rcases h_mem with ⟨d', h_chain, h_d'_le_d⟩
      have h_phi_le_d' := lemma_2_5_b 1 v d' h_chain
      simp only [inv_one, one_mul] at h_phi_le_d'
      exact le_trans h_phi_le_d' h_d'_le_d
    rw [IsMaximalIn]
    refine ⟨h_deg_le, ?_⟩
    intro x h_x_deg_le h_v_le_x
    have h_x_in_Re : x ∈ {w | ∃ d', HasChain 1 w d' ∧ d' ≤ d} := by
      use getDegree x
      exact ⟨trivial_chain x, h_x_deg_le⟩
    apply h_in_Re.2 x h_x_in_Re h_v_le_x
  · intro h_in_Ad
    simp only [Ad, one_mul, cs.length_one, zero_add, true_and] at h_in_Ad
    simp only [ReachableSet]
    constructor
    · use getDegree v
      exact ⟨trivial_chain v, h_in_Ad.1⟩
    · intro x h_in_Re h_v_lt_x
      have h_x_in_Ad : x ∈ {x | getDegree x ≤ d} := by
        change getDegree x ≤ d
        rcases h_in_Re with ⟨d', h_chain, h_d'_le_d⟩
        have h_phi_le_d' := lemma_2_5_b 1 x d' h_chain
        simp only [inv_one, one_mul] at h_phi_le_d'
        exact le_trans h_phi_le_d' h_d'_le_d
      apply h_in_Ad.2 x h_x_in_Ad h_v_lt_x

theorem curve_nbhd_one_diag (d : Degree) (p : d.a = d.b) :
  CurveNeighborhood 1 d = { s0s1_pow d.a, s1s0_pow d.a } := by
  rw [curve_nbhd_one_eq_max_ad_one]
  have h := max_ad_one_diag_iff_r_or_neg_r d.a
  ext v
  specialize h v
  simp_all only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  have hf : d = { a := d.b, b := d.b } := by
    ext <;> simp[p]
  rw [← hf] at h
  rw [h, s0s1_pow_equiv, s1s0_pow_equiv]

lemma s_alpha_d_maximal (d : Degree) (p : d.a ≠ d.b) :
  IsMaximalIn (s_alpha_d d) (Ad 1 d) := by
  by_cases h : d.a > d.b
  · have hs : s_alpha_d d = sr (-(d.b : ℤ)) := by
      unfold s_alpha_d s_α root_from_degree
      simp only [h, ↓reduceIte, Fin.isValue]
      have hsum : d.b + 1 + d.b = 2 * d.b + 1 := by omega
      rw [hsum, cs.prod_alternatingWord_eq_mul_pow 1 0 (2 * d.b + 1)]
      have hdiv : (2 * d.b + 1) / 2 = d.b := by omega
      rw [hdiv]
      simp only [not_even_bit1, ↓reduceIte, Fin.isValue, ← s0', s0, ← s1', s1, sr_mul_sr,
        zero_sub, r_pow, neg_mul, one_mul, sr_mul_r, zero_add]
      have hgt : d.b + 1 > d.b := by omega
      simp [hgt]
    rw [hs, ad_one_eq_degree_le]
    refine ⟨?_, ?_⟩
    · simp [getDegree_sr]
      omega
    · intro v hv hv_le
      have hv_le' : sr (-(d.b : ℤ)) ≤ v := by simpa [hs] using hv_le
      have hv_cmp : (ℓ (sr (-(d.b : ℤ))) < ℓ v) ∨ (sr (-(d.b : ℤ)) = v) := by
        rw [← lt_iff_length_lt]
        exact hv_le'
      cases v with
      | r n =>
        rw [length_sr_abs, length_r] at hv_cmp
        simp_all [getDegree_r]
        omega
      | sr n =>
        rcases hv_cmp with hlt | heq
        · rw [length_sr_abs, length_sr_abs] at hlt
          simp_all [getDegree_sr]
          omega
        · simpa using heq
  · have hs : s_alpha_d d = sr ((d.a : ℤ) + 1) := by
      unfold s_alpha_d s_α root_from_degree
      simp only [h, ↓reduceIte, Fin.isValue]
      have hsum : d.a + (d.a + 1) = 2 * d.a + 1 := by omega
      rw [hsum, cs.prod_alternatingWord_eq_mul_pow 0 1 (2 * d.a + 1)]
      have hdiv : (2 * d.a + 1) / 2 = d.a := by omega
      rw [hdiv]
      simp only [not_even_bit1, ↓reduceIte, Fin.isValue, ← s1', s1, ← s0', s0, sr_mul_sr,
        sub_zero, r_pow, one_mul, sr_mul_r]
      have hnot : ¬ d.a > d.a + 1 := by omega
      simp [hnot, add_comm]
    rw [hs, ad_one_eq_degree_le]
    refine ⟨?_, ?_⟩
    · simp [getDegree_sr]
      omega
    · intro v hv hv_le
      have hv_le' : sr (((d.a + 1 : ℕ) : ℤ)) ≤ v := by
        simpa [hs, add_comm] using hv_le
      have hv_cmp : (ℓ (sr (((d.a + 1 : ℕ) : ℤ))) < ℓ v) ∨
          (sr (((d.a + 1 : ℕ) : ℤ)) = v) := by
        rw [← lt_iff_length_lt]
        exact hv_le'
      cases v with
      | r n =>
        rw [length_sr_abs, length_r] at hv_cmp
        simp_all [getDegree_r]
        omega
      | sr n =>
        rcases hv_cmp with hlt | heq
        · rw [length_sr_abs, length_sr_abs] at hlt
          simp_all [getDegree_sr]
          omega
        · simpa using heq

theorem curve_nbhd_one_offdiag (d : Degree) (p : d.a ≠ d.b) :
    CurveNeighborhood 1 d = { s_alpha_d d } := by
    rw [curve_nbhd_one_eq_max_ad_one]
    ext v
    have h := exists_unique_max_ad_one_neq _ p
    constructor
    · simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      intro w
      rcases h with ⟨w1, w2, q⟩
      simp at q
      simp [q _ (s_alpha_d_maximal _ p), q _ w]
    · intro w
      simp at *
      simp [w, (s_alpha_d_maximal _ p)]

theorem curve_nbhd_one (d : Degree) :
    CurveNeighborhood 1 d =
      if d.a = d.b then
        { s0s1_pow d.a, s1s0_pow d.a }
      else
        { s_alpha_d d } := by
        split_ifs with h
        · exact curve_nbhd_one_diag d h
        · exact curve_nbhd_one_offdiag d h

def ends_in_s0 (u : D∞) : Prop := (reducedWord u).getLast? = some 0
def starts_with_s1 (v : D∞) : Prop := (reducedWord v).head? = some 1

lemma reducedWord_r_nonneg (k : ℤ) (hk : k ≥ 0) :
    reducedWord (r k) = alternatingWord 0 1 (2 * k.natAbs) := by
  simp [reducedWord, hk]

lemma reducedWord_r_neg (k : ℤ) (hk : ¬k ≥ 0) :
    reducedWord (r k) = alternatingWord 1 0 (2 * k.natAbs) := by
  simp [reducedWord, hk]

lemma reducedWord_sr_pos (k : ℤ) (hk : k > 0) :
    reducedWord (sr k) = alternatingWord 0 1 (2 * k.natAbs - 1) := by
  simp [reducedWord, hk]

lemma reducedWord_sr_nonpos (k : ℤ) (hk : ¬k > 0) :
    reducedWord (sr k) = alternatingWord 1 0 (2 * k.natAbs + 1) := by
  simp [reducedWord, hk]

lemma s_alpha_starts_with (α : Root) :
    (reducedWord (s_α α)).head? = some (if α.a > α.b then 0 else 1) := by
  unfold s_α
  split_ifs with h
  · rcases α.sub_one with hsub | hsub
    · have h_sum : α.a + α.b = 2 * α.b + 1 := by omega
      rw [h_sum]
      change (reducedWord (cs.wordProd (alternatingWord 1 0 (2 * α.b + 1)))).head? = some 0
      rw [alternating_reducedWord 1 0 (2 * α.b + 1) (by decide)]
      simpa using (alternatingWord_head_odd 1 0 α.b)
    · omega
  · rcases α.sub_one with hsub | hsub
    · omega
    · have h_sum : α.a + α.b = 2 * α.a + 1 := by omega
      rw [h_sum]
      change (reducedWord (cs.wordProd (alternatingWord 0 1 (2 * α.a + 1)))).head? = some 1
      rw [alternating_reducedWord 0 1 (2 * α.a + 1) (by decide)]
      simpa using (alternatingWord_head_odd 0 1 α.a)

lemma ends_in_s0_r (k : ℤ) : ends_in_s0 (r k) ↔ k < 0 := by
  unfold ends_in_s0
  constructor
  · intro h
    by_cases hk : k ≥ 0
    · rw [reducedWord_r_nonneg k hk] at h
      by_cases hk0 : k = 0
      · subst hk0
        exfalso
        simp [alternatingWord] at h
      · have hpos : k.natAbs > 0 := Int.natAbs_pos.mpr hk0
        have hlast := alternatingWord_getLast_pos 0 1 (2 * k.natAbs) (by omega)
        rw [hlast] at h
        exfalso
        simp at h
    · exact lt_of_not_ge hk
  · intro hk
    rw [reducedWord_r_neg k (not_le.mpr hk)]
    have hlast := alternatingWord_getLast_pos 1 0 (2 * k.natAbs) (by omega)
    simp [hlast]

lemma ends_in_s0_sr (k : ℤ) : ends_in_s0 (sr k) ↔ k ≤ 0 := by
  unfold ends_in_s0
  constructor
  · intro h
    by_cases hk : k > 0
    · rw [reducedWord_sr_pos k hk] at h
      have hlast := alternatingWord_getLast_pos 0 1 (2 * k.natAbs - 1) (by omega)
      rw [hlast] at h
      exfalso
      simp at h
    · exact le_of_not_gt hk
  · intro hk
    rw [reducedWord_sr_nonpos k (not_lt.mpr hk)]
    have hlast := alternatingWord_getLast_pos 1 0 (2 * k.natAbs + 1) (by omega)
    simp [hlast]

lemma starts_with_s1_r (k : ℤ) : starts_with_s1 (r k) ↔ k < 0 := by
  unfold starts_with_s1
  constructor
  · intro h
    by_cases hk : k ≥ 0
    · rw [reducedWord_r_nonneg k hk] at h
      by_cases hk0 : k = 0
      · subst hk0
        exfalso
        simp [alternatingWord] at h
      · have hpos : k.natAbs > 0 := Int.natAbs_pos.mpr hk0
        have hhead := alternatingWord_head_even_pos 0 1 k.natAbs hpos
        rw [hhead] at h
        exfalso
        simp at h
    · exact lt_of_not_ge hk
  · intro hk
    rw [reducedWord_r_neg k (not_le.mpr hk)]
    have hk0 : k ≠ 0 := ne_of_lt hk
    have hpos : k.natAbs > 0 := Int.natAbs_pos.mpr hk0
    have hhead := alternatingWord_head_even_pos 1 0 k.natAbs hpos
    simp [hhead]

lemma starts_with_s1_sr (k : ℤ) : starts_with_s1 (sr k) ↔ k > 0 := by
  unfold starts_with_s1
  constructor
  · intro h
    by_cases hk : k > 0
    · exact hk
    · rw [reducedWord_sr_nonpos k hk] at h
      have hhead := alternatingWord_head_odd 1 0 k.natAbs
      rw [hhead] at h
      exfalso
      simp at h
  · intro hk
    rw [reducedWord_sr_pos k hk]
    have hhead := alternatingWord_head_odd 0 1 (k.natAbs - 1)
    have hlen : 2 * k.natAbs - 1 = 2 * (k.natAbs - 1) + 1 := by omega
    simpa [hlen] using hhead

lemma length_add_of_ends_s0_starts_s1 (u v : Vertex)
    (hu : ends_in_s0 u) (hv : starts_with_s1 v) : ℓ (u * v) = ℓ u + ℓ v := by
  cases u with
  | r ku =>
    let ku' : ℤ := ku
    have hu' : ku' < 0 := by
      have : ends_in_s0 (r ku') := hu
      exact (ends_in_s0_r ku').mp this
    cases v with
    | r kv =>
      let kv' : ℤ := kv
      have hv' : kv' < 0 := by
        have : starts_with_s1 (r kv') := hv
        exact (starts_with_s1_r kv').mp this
      simp only [r_mul_r, length_r]
      have h : (ku' + kv').natAbs = ku'.natAbs + kv'.natAbs :=
        Int.natAbs_add_of_nonpos (le_of_lt hu') (le_of_lt hv')
      rw [h]
      ring
    | sr kv =>
      let kv' : ℤ := kv
      have hv' : kv' > 0 := by
        have : starts_with_s1 (sr kv') := hv
        exact (starts_with_s1_sr kv').mp this
      have h_pos : kv' - ku' > 0 := by linarith
      have h_natAbs : (kv' - ku').natAbs = kv'.natAbs + ku'.natAbs := by
        rw [show kv' - ku' = kv' + (-ku') by ring,
          Int.natAbs_add_of_nonneg (le_of_lt hv') (by linarith : (0 : ℤ) ≤ -ku'),
          Int.natAbs_neg]
      simp only [r_mul_sr, length_r, length_sr]
      split_ifs with h1
      · rw [h_natAbs]
        omega
      · exfalso
        exact h1 h_pos
  | sr ku =>
    let ku' : ℤ := ku
    have hu' : ku' ≤ 0 := by
      have : ends_in_s0 (sr ku') := hu
      exact (ends_in_s0_sr ku').mp this
    have h_u_not_pos : ¬(ku' > 0) := not_lt.mpr hu'
    cases v with
    | r kv =>
      let kv' : ℤ := kv
      have hv' : kv' < 0 := by
        have : starts_with_s1 (r kv') := hv
        exact (starts_with_s1_r kv').mp this
      have h_sum_not_pos : ¬(ku' + kv' > 0) := by linarith
      have h_natAbs : (ku' + kv').natAbs = ku'.natAbs + kv'.natAbs :=
        Int.natAbs_add_of_nonpos hu' (le_of_lt hv')
      simp only [sr_mul_r, length_sr, length_r]
      split_ifs with h1
      · exfalso
        exact h_sum_not_pos h1
      · rw [h_natAbs]
        omega
    | sr kv =>
      let kv' : ℤ := kv
      have hv' : kv' > 0 := by
        have : starts_with_s1 (sr kv') := hv
        exact (starts_with_s1_sr kv').mp this
      have h_natAbs : (kv' - ku').natAbs = kv'.natAbs + ku'.natAbs := by
        rw [show kv' - ku' = kv' + (-ku') by ring,
          Int.natAbs_add_of_nonneg (le_of_lt hv') (by linarith : (0 : ℤ) ≤ -ku'),
          Int.natAbs_neg]
      simp only [sr_mul_sr, length_r, length_sr]
      split_ifs with h1
      · exfalso
        exact h_u_not_pos h1
      · rw [h_natAbs]
        omega

lemma not_length_add_of_ends_s0_mul_r_pos (u : Vertex) (k : ℤ)
    (hu : ends_in_s0 u) (hk : 0 < k) :
    ℓ (u * r k) ≠ ℓ u + ℓ (r k) := by
  cases u with
  | r m =>
    let m' : ℤ := m
    have hm : m' < 0 := (ends_in_s0_r m').mp hu
    have hlen_u : ℓ (r m') = 2 * m'.natAbs := by simp [length_r]
    have hlen_v : ℓ (r k) = 2 * k.natAbs := by simp [length_r]
    have hlen_prod : ℓ (r m' * r k) = 2 * (m' + k).natAbs := by simp [r_mul_r, length_r]
    intro heq
    rw [hlen_u, hlen_v, hlen_prod] at heq
    have h_abs : (m' + k).natAbs ≤ m'.natAbs + k.natAbs := Int.natAbs_add_le m' k
    omega
  | sr m =>
    let m' : ℤ := m
    have hm : m' ≤ 0 := (ends_in_s0_sr m').mp hu
    have hlen_u : ℓ (sr m') = 2 * m'.natAbs + 1 := by
      simp [length_sr, not_lt.mpr hm]
    have hlen_v : ℓ (r k) = 2 * k.natAbs := by simp [length_r]
    have hlen_prod : ℓ (sr m' * r k)
        = (if m' + k > 0 then 2 * (m' + k).natAbs - 1 else 2 * (m' + k).natAbs + 1) := by
      simp [sr_mul_r, length_sr]
    intro heq
    rw [hlen_u, hlen_v, hlen_prod] at heq
    split_ifs at heq with hmk
    · have h_abs : (m' + k).natAbs ≤ m'.natAbs + k.natAbs := Int.natAbs_add_le m' k
      omega
    · have h_abs : (m' + k).natAbs ≤ m'.natAbs + k.natAbs := Int.natAbs_add_le m' k
      omega

lemma not_length_add_of_ends_s0_mul_sr_nonpos (u : Vertex) (k : ℤ)
    (hu : ends_in_s0 u) (hk : k ≤ 0) :
    ℓ (u * sr k) ≠ ℓ u + ℓ (sr k) := by
  cases u with
  | r m =>
    let m' : ℤ := m
    have hm : m' < 0 := (ends_in_s0_r m').mp hu
    have hlen_u : ℓ (r m') = 2 * m'.natAbs := by simp [length_r]
    have hlen_v : ℓ (sr k) = 2 * k.natAbs + 1 := by
      simp [length_sr, not_lt.mpr hk]
    have hlen_prod : ℓ (r m' * sr k)
        = (if k - m' > 0 then 2 * (k - m').natAbs - 1 else 2 * (k - m').natAbs + 1) := by
      simp [r_mul_sr, length_sr]
    intro heq
    rw [hlen_u, hlen_v, hlen_prod] at heq
    split_ifs at heq with hkm
    · have h_abs : (k - m').natAbs ≤ k.natAbs + m'.natAbs := Int.natAbs_sub_le k m'
      omega
    · have h_abs : (k - m').natAbs ≤ k.natAbs + m'.natAbs := Int.natAbs_sub_le k m'
      omega
  | sr m =>
    let m' : ℤ := m
    have hm : m' ≤ 0 := (ends_in_s0_sr m').mp hu
    have hlen_u : ℓ (sr m') = 2 * m'.natAbs + 1 := by
      simp [length_sr, not_lt.mpr hm]
    have hlen_v : ℓ (sr k) = 2 * k.natAbs + 1 := by
      simp [length_sr, not_lt.mpr hk]
    have hlen_prod : ℓ (sr m' * sr k) = 2 * (k - m').natAbs := by
      simp [sr_mul_sr, length_r]
    intro heq
    rw [hlen_u, hlen_v, hlen_prod] at heq
    have h_abs : (k - m').natAbs ≤ k.natAbs + m'.natAbs := Int.natAbs_sub_le k m'
    omega

theorem max_ad_b_gt_a_ends_s0 (u : Vertex) (d : Degree) (hu : ends_in_s0 u)
    (h : d.b > d.a) : IsMaximalIn (s_alpha_d d) (Ad u d) := by
  set w := s_alpha_d d with hw_def
  have hna : ¬(d.a > d.b) := not_lt.mpr (le_of_lt h)
  have h_root : root_from_degree d = ⟨d.a, d.a + 1, Or.inr rfl⟩ := by
    unfold root_from_degree
    simp only [hna, ↓reduceIte]
  have hw_eq : w = cs.wordProd (alternatingWord 0 1 (2 * d.a + 1)) := by
    rw [hw_def]
    unfold s_alpha_d s_α
    rw [h_root]
    have hnot : ¬d.a > d.a + 1 := Nat.not_lt.mpr (Nat.le_add_right d.a 1)
    have hsum : d.a + (d.a + 1) = 2 * d.a + 1 := by omega
    simp [hnot, hsum]
  have hw_sr : w = sr ((d.a : ℤ) + 1) := by
    rw [hw_eq, cs.prod_alternatingWord_eq_mul_pow 0 1 (2 * d.a + 1)]
    have h_div : (2 * d.a + 1) / 2 = d.a := by omega
    simp only [not_even_bit1, ↓reduceIte, Fin.isValue, ← s1', s1, ← s0', s0, sr_mul_sr,
      sub_zero, h_div, r_pow, one_mul, sr_mul_r]
    simp [add_comm]
  have hw_starts_s1 : starts_with_s1 w := by
    rw [hw_sr, starts_with_s1_sr]
    omega
  have h_len : ℓ (u * w) = ℓ u + ℓ w :=
    length_add_of_ends_s0_starts_s1 u w hu hw_starts_s1
  have h_deg : φ w ≤ d := by
    rw [hw_def]
    unfold s_alpha_d
    rw [h_root, φ_s_alpha_eq]
    simp only [Root.toDegree, Degreele_le_def, le_refl]
    constructor
    · trivial
    · exact h
  have hw_len : ℓ w = 2 * d.a + 1 := by
    rw [hw_sr, length_sr]
    have hpos : (d.a : ℤ) + 1 > 0 := by linarith
    simp only [hpos, ↓reduceIte]
    rw [show ((d.a : ℤ) + 1).natAbs = d.a + 1 by rfl]
    ring_nf
    exact succ_add_sub_one (d.a * 2) 1
  have hv_len_bound : ∀ v, v ∈ Ad u d → ℓ v ≤ 2 * d.a + 1 := by
    intro v ⟨_, hv_deg⟩
    cases v with
    | r k =>
      simp only [getDegree_r, Degreele_le_def] at hv_deg
      simp only [length_r]
      omega
    | sr k =>
      simp only [getDegree_sr, Degreele_le_def] at hv_deg
      simp only [length_sr]
      split_ifs with hk <;> omega
  constructor
  · exact ⟨h_len, h_deg⟩
  · intro v hv hv_le
    rcases hv_le with hv_lt | hv_eq
    · have hlen_lt : ℓ w < ℓ v := (lt_iff_length_lt w v).mp hv_lt
      have hlen_bound := hv_len_bound v hv
      rw [hw_len] at hlen_lt
      omega
    · exact hv_eq

theorem max_ad_a_gt_b_ends_s0 (u : Vertex) (d : Degree) (hu : ends_in_s0 u)
    (h : d.a > d.b) : IsMaximalIn (s0 * s_alpha_d d) (Ad u d) := by
  set w := s0 * s_alpha_d d with hw_def
  have h_root : root_from_degree d = ⟨d.b + 1, d.b, Or.inl rfl⟩ := by
    unfold root_from_degree
    simp only [h, ↓reduceIte]
  have hs_alpha : s_alpha_d d = sr (-(d.b : ℤ)) := by
    unfold s_alpha_d s_α
    rw [h_root]
    simp only [gt_iff_lt, lt_add_iff_pos_right, zero_lt_one, ↓reduceIte, Fin.isValue]
    have h_sum : d.b + 1 + d.b = 2 * d.b + 1 := by ring
    rw [h_sum, cs.prod_alternatingWord_eq_mul_pow 1 0 (2 * d.b + 1)]
    have h_div : (2 * d.b + 1) / 2 = d.b := by omega
    simp only [not_even_bit1, ↓reduceIte, Fin.isValue, ← s0', s0, ← s1', s1, sr_mul_sr,
      zero_sub, h_div, r_pow, neg_mul, one_mul, sr_mul_r, zero_add]
  have hw_r : w = r (-(d.b : ℤ)) := by
    rw [hw_def, hs_alpha]
    simp [s0, sr_mul_sr]
  by_cases hb_pos : d.b > 0
  · have hw_starts_s1 : starts_with_s1 w := by
      rw [hw_r, starts_with_s1_r]
      simp only [Left.neg_neg_iff, Nat.cast_pos]
      exact hb_pos
    have h_len : ℓ (u * w) = ℓ u + ℓ w :=
      length_add_of_ends_s0_starts_s1 u w hu hw_starts_s1
    have h_deg : φ w ≤ d := by
      rw [hw_r]
      simp only [getDegree_r, Int.natAbs_neg, Int.natAbs_natCast, Degreele_le_def, le_refl]
      exact ⟨le_of_lt h, trivial⟩
    have hw_len : ℓ w = 2 * d.b := by
      rw [hw_r, length_r]
      simp
    have hv_len_bound : ∀ v, v ∈ Ad u d → ℓ v ≤ 2 * d.b := by
      intro v ⟨hv_len_eq, hv_deg⟩
      cases v with
      | r k =>
        simp only [getDegree_r, Degreele_le_def] at hv_deg
        simp only [length_r]
        exact Nat.mul_le_mul_left 2 hv_deg.2
      | sr k =>
        simp only [getDegree_sr, Degreele_le_def] at hv_deg
        simp only [length_sr]
        split_ifs with hk
        · rcases hv_deg with ⟨_, h_les⟩
          calc 2 * k.natAbs - 1
            _ ≤ 2 * k.natAbs := Nat.sub_le _ _
            _ ≤ 2 * d.b := Nat.mul_le_mul_left 2 h_les
        · exfalso
          let k' : ℤ := k
          have hk' : k' ≤ 0 := by
            simpa [k', gt_iff_lt] using hk
          have hv_len_eq' : ℓ (u * sr k') = ℓ u + ℓ (sr k') := by
            simpa [k'] using hv_len_eq
          exact (not_length_add_of_ends_s0_mul_sr_nonpos u k' hu hk') hv_len_eq'
    constructor
    · exact ⟨h_len, h_deg⟩
    · intro v hv hv_le
      rcases hv_le with hv_lt | hv_eq
      · have hlen_lt : ℓ w < ℓ v := (lt_iff_length_lt w v).mp hv_lt
        have hlen_bound := hv_len_bound v hv
        rw [hw_len] at hlen_lt
        omega
      · exact hv_eq
  · have hb_zero : d.b = 0 := Nat.eq_zero_of_not_pos hb_pos
    have hw_one : w = 1 := by
      rw [hw_r, hb_zero]
      simp
    have hv_one : ∀ v, v ∈ Ad u d → v = 1 := by
      intro v ⟨hv_len_eq, hv_deg⟩
      have hv_len_zero : ℓ v = 0 := by
        cases v with
        | r k =>
          simp only [getDegree_r, Degreele_le_def, hb_zero] at hv_deg
          simp only [length_r]
          have : k.natAbs ≤ 0 := hv_deg.2
          have : k.natAbs = 0 := Nat.eq_zero_of_le_zero this
          linarith
        | sr k =>
          exfalso
          simp only [getDegree_sr, Degreele_le_def, hb_zero] at hv_deg
          rcases hv_deg with ⟨_, h⟩
          have hk_zero : k.natAbs = 0 := Nat.eq_zero_of_le_zero h
          have hk_eq : k = 0 := Int.natAbs_eq_zero.mp hk_zero
          subst hk_eq
          have hv_len_eq' : ℓ (u * sr (0 : ℤ)) = ℓ u + ℓ (sr (0 : ℤ)) := by
            simpa using hv_len_eq
          exact (not_length_add_of_ends_s0_mul_sr_nonpos u (0 : ℤ) hu (by omega)) hv_len_eq'
      exact (length_eq_zero_iff cs).mp hv_len_zero
    rw [hw_one]
    constructor
    · constructor
      · simp
      · simp only [Degreele_le_def]
        exact ⟨Nat.zero_le d.a, Nat.zero_le d.b⟩
    · intro v hv hv_le
      symm
      exact hv_one v hv

theorem max_ad_a_eq_b_ends_s0 (u : Vertex) (d : Degree) (hu : ends_in_s0 u)
    (h : d.a = d.b) : IsMaximalIn (s1 * s_alpha_d (d.sub {a := 0, b := 1})) (Ad u d) := by
  set a := d.a with ha_def
  set w := s1 * s_alpha_d (d.sub {a := 0, b := 1}) with hw_def
  by_cases ha_pos : a > 0
  · have h_dsub : d.sub {a := 0, b := 1} = ⟨a, a - 1⟩ := by
      simp only [Degree.sub, h, Nat.sub_zero]
      ext <;> simp only
      exact h
    have h_a_gt : a > a - 1 := Nat.sub_lt ha_pos (by omega)
    have h_root : root_from_degree (d.sub {a := 0, b := 1}) = ⟨a, a - 1, Or.inl (by omega)⟩ := by
      unfold root_from_degree
      rw [h_dsub]
      simp only [h_a_gt, ↓reduceIte]
      congr
      exact Nat.sub_add_cancel ha_pos
    have hs_alpha : s_alpha_d (d.sub {a := 0, b := 1}) = sr (1 - (a : ℤ)) := by
      unfold s_alpha_d s_α
      rw [h_root]
      simp only [gt_iff_lt, h_a_gt, ↓reduceIte, Fin.isValue]
      rw [show a + (a - 1) = 2 * (a - 1) + 1 by omega]
      rw [cs.prod_alternatingWord_eq_mul_pow 1 0 (2 * (a - 1) + 1)]
      have h_div : (2 * (a - 1) + 1) / 2 = a - 1 := by omega
      simp only [not_even_bit1, ↓reduceIte, Fin.isValue, ← s0', s0, ← s1', s1, sr_mul_sr,
        zero_sub, h_div, r_pow, neg_mul, one_mul, sr_mul_r, zero_add]
      have h1 : 1 ≤ a := ha_pos
      rw [Int.ofNat_sub h1]
      ring_nf
    have hw_r : w = r (-(a : ℤ)) := by
      rw [hw_def, hs_alpha, s1, sr_mul_sr]
      congr
      ring
    have hw_starts_s1 : starts_with_s1 w := by
      rw [hw_r, starts_with_s1_r]
      simp only [Left.neg_neg_iff, Nat.cast_pos]
      exact ha_pos
    have h_len : ℓ (u * w) = ℓ u + ℓ w :=
      length_add_of_ends_s0_starts_s1 u w hu hw_starts_s1
    have h_deg : φ w ≤ d := by
      rw [hw_r]
      simp only [getDegree_r, Int.natAbs_neg, Int.natAbs_natCast, Degreele_le_def]
      exact ⟨le_refl a, le_of_eq h⟩
    have hw_len : ℓ w = 2 * a := by
      rw [hw_r, length_r]
      simp
    have hv_len_bound : ∀ v, v ∈ Ad u d → ℓ v ≤ 2 * a := by
      intro v ⟨hv_len_eq, hv_deg⟩
      cases v with
      | r k =>
        let k' : ℤ := k
        by_cases hk_sign : 0 < k'
        · exfalso
          have hv_len_eq' : ℓ (u * r k') = ℓ u + ℓ (r k') := by
            simpa [k'] using hv_len_eq
          exact (not_length_add_of_ends_s0_mul_r_pos u k' hu hk_sign) hv_len_eq'
        · simp only [getDegree_r, Degreele_le_def] at hv_deg
          simp only [length_r]
          exact Nat.mul_le_mul_left 2 hv_deg.1
      | sr k =>
        let k' : ℤ := k
        by_cases hk_pos : k' > 0
        · simp only [length_sr]
          simp only [getDegree_sr, Degreele_le_def] at hv_deg
          have h1 : 2 * k'.natAbs - 1 ≤ 2 * k'.natAbs := Nat.sub_le _ _
          have h2 : 2 * k'.natAbs ≤ 2 * a := by linarith
          split_ifs <;> omega
        · exfalso
          have hk_le : k' ≤ 0 := not_lt.mp hk_pos
          have hv_len_eq' : ℓ (u * sr k') = ℓ u + ℓ (sr k') := by
            simpa [k'] using hv_len_eq
          exact (not_length_add_of_ends_s0_mul_sr_nonpos u k' hu hk_le) hv_len_eq'
    constructor
    · exact ⟨h_len, h_deg⟩
    · intro v hv hv_le
      rcases hv_le with hv_lt | hv_eq
      · have hlen_lt : ℓ w < ℓ v := (lt_iff_length_lt w v).mp hv_lt
        have hlen_bound := hv_len_bound v hv
        rw [hw_len] at hlen_lt
        omega
      · exact hv_eq
  · have ha_zero : a = 0 := Nat.eq_zero_of_not_pos ha_pos
    have hd_zero : d = ⟨0, 0⟩ := by
      ext <;> simp only
      · exact ha_zero
      · rw [← h, ha_zero]
    have h_dsub : d.sub {a := 0, b := 1} = ⟨0, 0⟩ := by
      rw [hd_zero]
      rfl
    have hs_alpha : s_alpha_d (d.sub {a := 0, b := 1}) = s1 := by
      rw [h_dsub]
      decide
    have hw_one : w = 1 := by
      rw [hw_def, hs_alpha, s1]
      simp
    rw [hw_one]
    have hv_must_be_one : ∀ v, v ∈ Ad u d → v = 1 := by
      intro v ⟨hv_len_eq, hv_deg⟩
      rw [hd_zero] at hv_deg
      simp only [Degreele_le_def] at hv_deg
      have ha_zero' : (φ v).a = 0 := Nat.eq_zero_of_le_zero hv_deg.1
      have hb_zero : (φ v).b = 0 := Nat.eq_zero_of_le_zero hv_deg.2
      cases v with
      | r k =>
        simp only [getDegree_r] at ha_zero'
        have hk_zero : k = 0 := Int.natAbs_eq_zero.mp ha_zero'
        simp [hk_zero]
      | sr k =>
        simp only [getDegree_sr] at hb_zero
        have hk_zero : k = 0 := Int.natAbs_eq_zero.mp hb_zero
        simp only [getDegree_sr, hk_zero] at ha_zero'
        norm_num at ha_zero'
    constructor
    · constructor
      · simp
      · rw [hd_zero]
        simp only [getDegree_one, le_refl]
    · intro v hv hv_le
      symm
      exact hv_must_be_one v hv

theorem max_ad_ends_s0 (u : Vertex) (d : Degree) (hu : ends_in_s0 u) :
  IsMaximalIn
    (if d.a = d.b then s1 * s_alpha_d (d.sub {a := 0, b := 1})
     else if d.b > d.a then s_alpha_d d
     else s0 * s_alpha_d d)
    (Ad u d) := by
  split_ifs with h1 h2
  · exact max_ad_a_eq_b_ends_s0 u d hu h1
  · exact max_ad_b_gt_a_ends_s0 u d hu h2
  · have h3 : d.a > d.b := Nat.lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1)
    exact max_ad_a_gt_b_ends_s0 u d hu h3


lemma edge_left_mul (g u v : Vertex) (α : Root) (h : IsEdge u v α) :
    IsEdge (g * u) (g * v) α := by
  dsimp [IsEdge] at *
  rw [h, mul_assoc]

lemma chain_left_mul (g u v : Vertex) (d : Degree) (h : HasChain u v d) :
    HasChain (g * u) (g * v) d := by
  induction h with
  | refl  =>
    exact HasChain.refl (g * u)
  | step h_prev h_edge ih =>
    apply HasChain.step ih (edge_left_mul g _ _ _ h_edge)

lemma CurveNeighborhood_max (h : v ∈ CurveNeighborhood u d) :
     ∀ w ∈ ReachableSet u d, ℓ w ≤ ℓ v := by
  rw [CurveNeighborhood] at h
  intro w hw
  by_contra h_lt
  rw [not_le, ← lt_iff_length_lt] at h_lt
  have h_le : v ≤ w := le_of_lt h_lt
  have h_eq := h.2 w hw h_le
  rw [h_eq] at h_lt
  exact (lt_self_iff_false w).mp h_lt

theorem len_mul_ad_le_curve_nbhd_max (u : Vertex) (d : Degree) (z : Vertex) (v : Vertex)
    (hz : z ∈ Ad 1 d) (hv : v ∈ CurveNeighborhood u d) :
    ℓ (u * z) ≤ ℓ v := by
  have h_deg_z : φ z ≤ d := by
      simp only [Ad, one_mul, length_one, zero_add, Degreele_le_def, true_and,
        Set.mem_setOf_eq] at hz
      exact ⟨hz.1,hz.2⟩
  have h_chain_z : HasChain 1 z (φ z) := trivial_chain z
  have h_chain_uz : HasChain u (u * z) (getDegree z) :=by
    have := chain_left_mul u 1 z _ h_chain_z
    simp only [mul_one] at this
    exact this
  have h_uz_in_Re : u * z ∈ ReachableSet u d := by
    use getDegree z
  exact CurveNeighborhood_max hv (u * z) h_uz_in_Re

theorem deg_inv_mul_le_curve_nbhd (u : Vertex) (d : Degree) (v : Vertex)
     (hv : v ∈ CurveNeighborhood u d) :
   φ (u⁻¹ * v) ≤ d := by
  have h_v_reachable : v ∈ ReachableSet u d := by
    rw [CurveNeighborhood] at hv
    exact hv.1
  rcases h_v_reachable with ⟨dv, h_chain_v, h_dv_le_d⟩
  have h_chain_inv_u_v : HasChain (u⁻¹ * u) (u⁻¹ * v) dv := chain_left_mul u⁻¹ u v dv h_chain_v
  simp only [inv_mul_cancel] at h_chain_inv_u_v
  have h_phi_le_dv := lemma_2_5_b 1 (u⁻¹ * v) dv h_chain_inv_u_v
  simp only [inv_one, one_mul, Degreele_le_def] at h_phi_le_dv
  exact le_trans h_phi_le_dv h_dv_le_d

theorem inv_mul_len_le_curve_nbhd_one_max (u : Vertex) (d : Degree) (z : Vertex) (v : Vertex)
    (hz : z ∈ CurveNeighborhood 1 d) (hv : v ∈ CurveNeighborhood u d) :
    ℓ (u⁻¹ * v) ≤ ℓ z := by
  rw [CurveNeighborhood] at hv
  rcases hv with ⟨h_v_in_Re, -⟩
  rcases h_v_in_Re with ⟨dv, h_chain_v, h_dv_le_d⟩
  have h_chain_inv : HasChain (u⁻¹ * u) (u⁻¹ * v) dv := chain_left_mul u⁻¹ u v dv h_chain_v
  simp only [inv_mul_cancel] at h_chain_inv
  set w := u⁻¹ * v with hw
  have h_w_in_Re : w ∈ ReachableSet 1 d := by use dv
  apply CurveNeighborhood_max hz w h_w_in_Re

lemma left_descent_0_r_pos (k : ℤ)
    (h : cs.IsLeftDescent (r k) (0 : Fin 2)) : 0 < k := by
  rw [cs.isLeftDescent_iff] at h
  have hs : cs.simple 0 = s0 := rfl
  simp only [Fin.isValue, length_r] at h
  rw [hs, s0, sr_mul_r, zero_add, length_sr] at h
  split_ifs at h with hk <;> omega

lemma left_descent_0_sr_nonpos (k : ℤ)
    (h : cs.IsLeftDescent (sr k) (0 : Fin 2)) : k ≤ 0 := by
  rw [cs.isLeftDescent_iff] at h
  have hs : cs.simple 0 = s0 := rfl
  simp only [Fin.isValue, length_sr, gt_iff_lt] at h
  rw [hs, s0, sr_mul_sr, sub_zero, length_r] at h
  split_ifs at h with hk <;> omega

lemma left_descent_1_r_neg (k : ℤ)
    (h : cs.IsLeftDescent (r k) (1 : Fin 2)) : k < 0 := by
  rw [cs.isLeftDescent_iff] at h
  have hs : cs.simple 1 = s1 := rfl
  simp only [Fin.isValue, length_r] at h
  rw [hs, s1, sr_mul_r, length_sr] at h
  split_ifs at h with hk <;> omega

lemma left_descent_1_sr_pos (k : ℤ)
    (h : cs.IsLeftDescent (sr k) (1 : Fin 2)) : 0 < k := by
  rw [cs.isLeftDescent_iff] at h
  have hs : cs.simple 1 = s1 := rfl
  simp only [Fin.isValue, length_sr, gt_iff_lt] at h
  rw [hs, s1, sr_mul_sr, length_r] at h
  split_ifs at h with hk <;> omega

lemma degree_le_of_left_descent (i : Fin 2) (z : D∞)
    (hi : cs.IsLeftDescent z i) : φ (f i * z) ≤ φ z := by
  fin_cases i
  · cases z with
    | r k =>
      simp only [f, s0, getDegree_r, Degreele_le_def, Fin.zero_eta,
        Fin.isValue, Matrix.cons_val_zero, sr_mul_r, zero_add, getDegree_sr]
      have := left_descent_0_r_pos k hi
      constructor <;> omega
    | sr k =>
      simp only [f, s0, getDegree_sr, Degreele_le_def, Fin.zero_eta, Fin.isValue,
        Matrix.cons_val_zero, sr_mul_sr, sub_zero, getDegree_r, le_refl, and_true]
      have := left_descent_0_sr_nonpos k hi
      omega
  · cases z with
    | r k =>
      simp only [f, s1, getDegree_r, Degreele_le_def, Fin.mk_one, Fin.isValue,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, sr_mul_r, getDegree_sr]
      have := left_descent_1_r_neg k hi
      constructor <;> omega
    | sr k =>
      simp only [f, s1, getDegree_sr, Degreele_le_def, Fin.mk_one, Fin.isValue,
        Matrix.cons_val_one, Matrix.cons_val_fin_one, sr_mul_sr, getDegree_r, le_refl, true_and]
      have := left_descent_1_sr_pos k hi
      have : (k - 1).natAbs = k.natAbs - 1 := by omega
      rw [this]
      omega

lemma ends_in_s0_of_not_reduced_descent_0 (u z : D∞)
    (h_nr : ℓ (u * z) < ℓ u + ℓ z) (hi : cs.IsLeftDescent z (0 : Fin 2)) :
    ends_in_s0 u := by
  cases u with
  | r ku =>
    cases z with
    | r kz =>
      simp only [r_mul_r, length_r] at h_nr
      rw [ends_in_s0_r]
      have := left_descent_0_r_pos kz hi
      by_contra h
      push_neg at h
      omega
    | sr kz =>
      simp only [r_mul_sr, length_r, length_sr] at h_nr
      rw [ends_in_s0_r]
      have := left_descent_0_sr_nonpos kz hi
      by_contra h
      push_neg at h
      split_ifs at h_nr <;> omega
  | sr ku =>
    cases z with
    | r kz =>
      have := left_descent_0_r_pos kz hi
      rw [ends_in_s0_sr]
      simp only [sr_mul_r, length_sr, length_r] at h_nr
      by_contra h
      push_neg at h
      split_ifs at h_nr with h_sum_pos
      · omega
      · push_neg at h_sum_pos
        omega
    | sr kz =>
      simp only [sr_mul_sr, length_r, length_sr] at h_nr
      rw [ends_in_s0_sr]
      have := left_descent_0_sr_nonpos kz hi
      by_contra h
      push_neg at h
      split_ifs at h_nr with h1 h2 <;> omega

lemma not_ends_in_s0_of_not_reduced_descent_1 (u z : D∞)
    (h_nr : ℓ (u * z) < ℓ u + ℓ z) (hi : cs.IsLeftDescent z (1 : Fin 2)) :
    ¬ends_in_s0 u := by
  cases u with
  | r ku =>
    cases z with
    | r kz =>
      simp only [r_mul_r, length_r] at h_nr
      simp only [ends_in_s0_r, not_lt]
      have := left_descent_1_r_neg kz hi
      by_contra h
      push_neg at h
      have := Int.natAbs_add_of_nonpos (le_of_lt h) (le_of_lt this)
      omega
    | sr kz =>
      simp only [r_mul_sr, length_r, length_sr] at h_nr
      simp only [ends_in_s0_r, not_lt]
      have := left_descent_1_sr_pos kz hi
      by_contra h
      push_neg at h
      split_ifs at h_nr with h1 <;> omega
  | sr ku =>
    cases z with
    | r kz =>
      simp only [sr_mul_r, length_sr, length_r] at h_nr
      simp only [ends_in_s0_sr, not_le]
      have := left_descent_1_r_neg kz hi
      by_contra h
      push_neg at h
      have := Int.natAbs_add_of_nonpos h (le_of_lt this)
      split_ifs at h_nr <;> omega
    | sr kz =>
      simp only [sr_mul_sr, length_sr, length_r] at h_nr
      simp only [ends_in_s0_sr, not_le]
      have := left_descent_1_sr_pos kz hi
      by_contra h
      push_neg at h
      split_ifs at h_nr with h1 <;> omega

lemma starts_with_s1_of_s0_mul (z : D∞)
    (hi : cs.IsLeftDescent z (0 : Fin 2)) (hne : f 0 * z ≠ 1) :
    starts_with_s1 (f 0 * z) := by
  cases z with
  | r k =>
    simp only [f, s0, Fin.isValue, Matrix.cons_val_zero, sr_mul_r, zero_add]
    rw [starts_with_s1_sr]
    exact left_descent_0_r_pos k hi
  | sr k =>
    simp only [f, s0, Fin.isValue, Matrix.cons_val_zero,
      sr_mul_sr, sub_zero] at hne ⊢
    rw [starts_with_s1_r]
    have hle := left_descent_0_sr_nonpos k hi
    have hne0 : k ≠ 0 := by
      intro h
      apply hne
      rw [h]
      exact r_zero
    exact Std.lt_of_le_of_ne hle hne0

lemma not_starts_with_s1_of_s1_mul (z : D∞)
    (hi : cs.IsLeftDescent z (1 : Fin 2)) :
    ¬starts_with_s1 (f 1 * z) := by
  cases z with
  | r k =>
    simp only [f, s1, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, sr_mul_r]
    intro h
    rw [starts_with_s1_sr] at h
    have := left_descent_1_r_neg k hi
    omega
  | sr k =>
    simp only [f, s1, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, sr_mul_sr]
    intro h
    rw [starts_with_s1_r] at h
    have := left_descent_1_sr_pos k hi
    omega

lemma length_add_of_not_ends_s0_not_starts_s1 (u v : Vertex)
    (hu : ¬ends_in_s0 u) (hv : ¬starts_with_s1 v) : ℓ (u * v) = ℓ u + ℓ v := by
  cases u with
  | r ku =>
    simp only [ends_in_s0_r, not_lt] at hu
    cases v with
    | r kv =>
      simp only [starts_with_s1_r, not_lt] at hv
      simp only [r_mul_r, length_r]
      rw [Int.natAbs_add_of_nonneg hu hv]
      ring
    | sr kv =>
      simp only [starts_with_s1_sr, gt_iff_lt, not_lt] at hv
      simp only [r_mul_sr, length_r, length_sr]
      split_ifs <;> omega
  | sr ku =>
    simp only [ends_in_s0_sr, not_le] at hu
    cases v with
    | r kv =>
      simp only [starts_with_s1_r, not_lt] at hv
      simp only [sr_mul_r, length_sr, length_r]
      split_ifs <;> omega
    | sr kv =>
      simp only [starts_with_s1_sr, gt_iff_lt, not_lt] at hv
      simp only [sr_mul_sr, length_sr, length_r]
      split_ifs <;> omega

theorem inv_mul_mem_ad_curve_nbhd (u v : Vertex) (d : Degree) (hv : v ∈ CurveNeighborhood u d) :
    (u⁻¹ * v) ∈ Ad u d := by
  constructor
  · by_cases hu_1 : u = 1
    · simp [hu_1]
    · by_contra h_eq1
      simp only [mul_inv_cancel_left] at h_eq1
      set w := u⁻¹ * v with hw_def
      have h_le : ℓ v ≤ ℓ u + ℓ w := by
        calc
          ℓ v = ℓ (u * w) := by simp [hw_def]
          _ ≤ ℓ u + ℓ w := lemma_2_1_3 u w
      have h_lt : ℓ v < ℓ u + ℓ w := lt_of_le_of_ne h_le h_eq1
      have h_u_le_v : ℓ u ≤ ℓ v := by
        have h_u_reach : u ∈ ReachableSet u d := ⟨0, HasChain.refl u, by
          simp only [Degreele_le_def]
          constructor <;> exact le_of_ble_eq_true rfl⟩
        exact CurveNeighborhood_max hv u h_u_reach
      have h_inv_len : ℓ u⁻¹ = ℓ u := (lemma_2_1_1 u).symm
      have h_inv_le : ℓ u⁻¹ ≤ ℓ v := by
        rw [h_inv_len]
        exact h_u_le_v
      have h_dichotomy := length_mul_eq_add_or_sub u⁻¹ v h_inv_le
      rcases h_dichotomy with (h_add | h_sub)
      · rw [h_inv_len] at h_add
        have h_Gamma_nonempty : (CurveNeighborhood 1 d).Nonempty := by
          rw [curve_nbhd_one]
          split_ifs with h
          · exact ⟨s0s1_pow d.a, Set.mem_insert _ _⟩
          · exact ⟨s_alpha_d d, Set.mem_singleton _⟩
        obtain ⟨z, hz⟩ := h_Gamma_nonempty
        have hz_Ad : z ∈ Ad 1 d := by
          rw [curve_nbhd_one_eq_max_ad_one] at hz
          exact hz.1
        have h_uz_le_v : ℓ (u * z) ≤ ℓ v := len_mul_ad_le_curve_nbhd_max u d z v hz_Ad hv
        have h_w_le_z : ℓ w ≤ ℓ z := inv_mul_len_le_curve_nbhd_one_max u d z v hz hv
        have h_uv_le_z : ℓ u + ℓ v ≤ ℓ z := by
          rw [← h_add]
          exact h_w_le_z
        have h_uz_not_reduced : ℓ (u * z) < ℓ u + ℓ z := by
          calc
            ℓ (u * z) ≤ ℓ v := h_uz_le_v
            _ < ℓ u + ℓ w := h_lt
            _ ≤ ℓ u + ℓ z := by linarith [h_w_le_z]
        have h_u_pos : ℓ u ≥ 1 := by
          by_contra h
          push_neg at h
          have : ℓ u = 0 := lt_one_iff.mp h
          exact hu_1 ((length_eq_zero_iff cs).mp this)
        have hz_ne : z ≠ 1 := by
          intro h
          rw [h, cs.length_one] at h_uv_le_z
          linarith
        have h_exists_z' : ∃ z' ∈ Ad 1 d, ℓ z' = ℓ z - 1 ∧ ℓ (u * z') = ℓ u + ℓ z' := by
          obtain ⟨i, hi_left⟩ := cs.exists_leftDescent_of_ne_one hz_ne
          set z' := cs.simple i * z with hz'_def
          use z'
          have hs : cs.simple i = f i := by
            fin_cases i <;> rfl
          have h_z'_len : ℓ z' = ℓ z - 1 := by
            rw [cs.isLeftDescent_iff] at hi_left
            calc
              ℓ z' = ℓ (cs.simple i * z) := by rw [hz'_def]
              _ = ℓ z - 1 := Nat.eq_sub_of_add_eq hi_left
          have h_z'_deg : φ z' ≤ d := by
            have : φ z' ≤ φ z := by
              rw [hz'_def, hs]
              exact degree_le_of_left_descent i z hi_left
            exact le_trans this hz_Ad.2
          have h_prod : ℓ (u * z') = ℓ u + ℓ z' := by
            by_cases hz'_one : z' = 1
            · simp [hz'_one]
            · rw [hs] at hz'_def
              fin_cases i
              · exact length_add_of_ends_s0_starts_s1 u z'
                  (ends_in_s0_of_not_reduced_descent_0 u z h_uz_not_reduced hi_left)
                  (by
                    rw [hz'_def]
                    exact starts_with_s1_of_s0_mul z hi_left (fun h => hz'_one (hz'_def.trans h)))
              · exact length_add_of_not_ends_s0_not_starts_s1 u z'
                  (not_ends_in_s0_of_not_reduced_descent_1 u z h_uz_not_reduced hi_left)
                  (by
                    rw [hz'_def]
                    exact not_starts_with_s1_of_s1_mul z hi_left)
          refine ⟨?_, h_z'_len, h_prod⟩
          simp only [Ad, one_mul, length_one, zero_add, true_and, Set.mem_setOf_eq]
          exact h_z'_deg
        obtain ⟨z', hz'_Ad, hz'_len, hz'_reduced⟩ := h_exists_z'
        have h_uz'_le_v : ℓ (u * z') ≤ ℓ v := len_mul_ad_le_curve_nbhd_max u d z' v hz'_Ad hv
        have h_bound1 : ℓ u + ℓ z - 1 ≤ ℓ v := by
          calc
            ℓ u + ℓ z - 1 = ℓ u + (ℓ z - 1) := by omega
            _ = ℓ u + ℓ z' := by rw [hz'_len]
            _ = ℓ (u * z') := hz'_reduced.symm
            _ ≤ ℓ v := h_uz'_le_v
        have h_bound2 : ℓ v ≤ ℓ z - ℓ u := Nat.le_sub_of_add_le' h_uv_le_z
        have h_contra : 2 * ℓ u ≤ 1 := by
          have : ℓ u + ℓ z - 1 ≤ ℓ z - ℓ u := le_trans h_bound1 h_bound2
          omega
        linarith
      · rw [h_inv_len, ← hw_def] at h_sub
        have : ℓ v = ℓ u + ℓ w := (Nat.sub_eq_iff_eq_add' h_u_le_v).mp (id (Eq.symm h_sub))
        contradiction
  · exact deg_inv_mul_le_curve_nbhd u d v hv

lemma Ad_u_in_Ad_one (u : Vertex) (d : Degree) (v : Vertex) (h : v ∈ Ad u d) : v ∈ Ad 1 d := by
  rw [Ad] at *
  simp only [one_mul, cs.length_one, zero_add, Set.mem_setOf_eq]
  exact And.imp_left (fun a ↦ trivial) h

lemma exists_max_in_Ad (u : Vertex) (d : Degree) (z : Vertex) (hz : z ∈ Ad u d) :
    ∃ w, IsMaximalIn w (Ad u d) ∧ z ≤ w := by
  let S_ge_z := { w ∈ Ad u d | z ≤ w }
  have h_fin : S_ge_z.Finite := h_finite.subset (Set.sep_subset _ _)
  have h_nonempty : S_ge_z.Nonempty := ⟨z, hz, le_refl z⟩
  obtain ⟨m, ⟨hm_in_Ad, h_z_le_m⟩, hm_max_in_subset⟩ :=
    Set.Finite.exists_maximalFor (id) S_ge_z h_fin h_nonempty
  use m
  constructor
  · rw [IsMaximalIn]
    constructor
    · exact hm_in_Ad
    · intro v' hv' hm_le_v'
      have h_v'_in_subset : v' ∈ S_ge_z := by
        constructor
        · exact hv'
        · exact le_trans h_z_le_m hm_le_v'
      have := hm_max_in_subset h_v'_in_subset hm_le_v'
      simp only [id_eq] at this
      exact le_antisymm hm_le_v' this
  · exact h_z_le_m

lemma reachable_of_Ad (u : Vertex) (d : Degree) (w : Vertex) (h : w ∈ Ad u d) :
    u * w ∈ ReachableSet u d := by
  have c1 := trivial_chain w
  have c2 := chain_left_mul u 1 w (getDegree w) c1
  simp only [mul_one] at c2
  use getDegree w
  exact ⟨c2, h.2⟩

lemma mul_le_mul_left_of_length_add (u : Vertex) (x y : Vertex)
    (hx : ℓ (u * x) = ℓ u + ℓ x) (hy : ℓ (u * y) = ℓ u + ℓ y) :
    x ≤ y ↔ u * x ≤ u * y := by
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq, lt_iff_length_lt, lt_iff_length_lt, hx, hy]
  constructor
  · rintro (h | rfl)
    · left; omega
    · right; rfl
  · rintro (h | h)
    · left; omega
    · right; exact mul_left_cancel h

lemma Lt_iff_le_and_ne (a b : Vertex) : Lt a b ↔ a ≤ b ∧ a ≠ b := by
  rw [Lt, le_iff_lt_or_eq]
  constructor
  · intro h
    constructor
    · left; exact h
    · rcases h with ⟨d, chain, ne⟩
      exact ne
  · rintro ⟨(h_lt | h_eq), h_ne⟩
    · exact h_lt
    · contradiction

lemma exists_max_ge_in_Reachable (u : Vertex) (d : Degree) (v : Vertex)
    (h : v ∈ ReachableSet u d) :
    ∃ m, m ∈ CurveNeighborhood u d ∧ v ≤ m := by
  let S_bound := { x : Vertex | φ (u⁻¹ * x) ≤ d }
  have h_bound_finite : S_bound.Finite := by
    let pre_image := { y : Vertex | φ y ≤ d }
    have h_pre_finite : pre_image.Finite := by
      have heq : pre_image = Ad 1 d := (ad_one_eq_degree_le d).symm
      rw [heq]
      exact h_finite
    have : S_bound = (fun y => u * y) '' pre_image := by
       ext x
       simp [S_bound, pre_image]
    rw [this]
    exact Set.Finite.image _ h_pre_finite
  have h_subset : ReachableSet u d ⊆ S_bound := by
    intro x hx
    rcases hx with ⟨dx, chain, h_dx_le_d⟩
    have chain_inv := chain_left_mul u⁻¹ u x dx chain
    simp only [inv_mul_cancel] at chain_inv
    have h_phi := lemma_2_5_b 1 (u⁻¹ * x) dx
    simp only [inv_one, one_mul] at h_phi
    exact le_trans (h_phi chain_inv) h_dx_le_d
  let S_ge_v := { m ∈ ReachableSet u d | v ≤ m }
  have h_fin_sub : S_ge_v.Finite :=by
    apply Set.Finite.subset h_bound_finite
    intro x ⟨hx_reach, _⟩
    exact h_subset hx_reach
  have h_nonempty : S_ge_v.Nonempty := ⟨v, h, le_refl v⟩
  obtain ⟨m, ⟨hm_reach, h_v_le_m⟩, hm_max⟩ :=
    Set.Finite.exists_maximalFor id S_ge_v h_fin_sub h_nonempty
  use m
  constructor
  · rw [CurveNeighborhood]
    constructor
    · exact hm_reach
    · intro v' hv' hm_le_v'
      have h_v'_in_S : v' ∈ S_ge_v := ⟨hv', le_trans h_v_le_m hm_le_v'⟩
      have := hm_max h_v'_in_S hm_le_v'
      simp only [id_eq] at this
      exact le_antisymm hm_le_v' this
  · exact h_v_le_m

theorem curve_nbhd_eq_mul_max_ad (u : Vertex) (d : Degree) :
    CurveNeighborhood u d = { v | ∃ w, IsMaximalIn w (Ad u d) ∧ v = u * w } := by
  apply Set.ext
  intro v
  constructor
  · intro hv
    have h_z_in_Ad : (u⁻¹ * v) ∈ Ad u d := inv_mul_mem_ad_curve_nbhd u v d hv
    let z := u⁻¹ * v
    have h_v_eq : v = u * z := by simp [z]
    obtain ⟨w, hw_max, h_z_le_w⟩ := exists_max_in_Ad u d z h_z_in_Ad
    have hw_in_Ad1 : w ∈ Ad 1 d := Ad_u_in_Ad_one u d w hw_max.1
    have h_len_uw_le_v := len_mul_ad_le_curve_nbhd_max u d w v hw_in_Ad1 hv
    have h_len_v : ℓ v = ℓ u + ℓ z := by
      rw [h_v_eq]
      exact h_z_in_Ad.1
    have h_len_uw : ℓ (u * w) = ℓ u + ℓ w := hw_max.1.1
    rw [h_len_v, h_len_uw] at h_len_uw_le_v
    have h_len_w_le_z : ℓ w ≤ ℓ z := Nat.le_of_add_le_add_left h_len_uw_le_v
    have h_z_eq_w : z = w := by
      by_contra h_neq
      have h_lt : z < w := lt_of_le_of_ne h_z_le_w h_neq
      have h_len_lt : ℓ z < ℓ w := by
        rw [← lt_iff_length_lt]
        exact h_lt
      linarith [h_len_lt, h_len_w_le_z]
    use w
    constructor
    · exact hw_max
    · rw [h_v_eq, h_z_eq_w]
  · rintro ⟨w, hw_max, rfl⟩
    have h_reach : u * w ∈ ReachableSet u d := reachable_of_Ad u d w hw_max.1
    rw [CurveNeighborhood]
    refine ⟨h_reach, ?_⟩
    intro v' h_reach_v' h_le_v_v'
    obtain ⟨m, hm_max, h_v'_le_m⟩ := exists_max_ge_in_Reachable u d v' h_reach_v'
    have h_m_in_gamma : m ∈ CurveNeighborhood u d := hm_max
    have h_z'_in_Ad : (u⁻¹ * m) ∈ Ad u d := inv_mul_mem_ad_curve_nbhd u m d h_m_in_gamma
    let w' := u⁻¹ * m
    have h_m_eq : m = u * w' := by simp [w']
    have h_uw_le_uw' : u * w ≤ u * w' :=
        le_trans h_le_v_v' (by rw [h_m_eq] at h_v'_le_m; exact h_v'_le_m)
    have h_w_le_w' : w ≤ w' := by
      rw [← mul_le_mul_left_of_length_add u w w' hw_max.1.1 h_z'_in_Ad.1] at h_uw_le_uw'
      exact h_uw_le_uw'
    have h_w_eq_w' : w = w' :=
      hw_max.2 w' h_z'_in_Ad h_w_le_w'
    have h_v_eq_m : u * w = m := by rw [h_m_eq, ←h_w_eq_w']
    have h_v'_eq_v : v' = u * w := by
      have h_m_eq_uw : m = u * w := h_v_eq_m.symm
      rw [h_m_eq_uw] at h_v'_le_m
      exact le_antisymm h_v'_le_m h_le_v_v'
    rw [h_v'_eq_v]

example : CurveNeighborhood 1 {a := 2, b := 2} = { s0s1_pow 2, s1s0_pow 2 } := by
  rw [curve_nbhd_one_diag {a := 2, b := 2} rfl]

example : CurveNeighborhood s0 {a := 2, b := 3} = {s0 * s_alpha_d {a := 2, b := 3}} := by
  rw [curve_nbhd_eq_mul_max_ad s0 {a := 2, b := 3}]
  have h_ends : ends_in_s0 s0 := by
    rw [s0, ends_in_s0_sr]
  have h_u_ne_1 : s0 ≠ 1 := by
    decide
  have h_max := max_ad_ends_s0 s0 {a := 2, b := 3} h_ends
  rw [if_neg (by norm_num), if_pos (by norm_num)] at h_max
  have h_unique := exists_unique_max_ad_ne_one s0 {a := 2, b := 3} h_u_ne_1
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w, hw_is_max, rfl⟩
    have h_w_eq : w = s_alpha_d {a := 2, b := 3} := by
      rcases h_unique with ⟨m, hm, h_uniq_eq⟩
      have h1 : w = m := by exact h_uniq_eq w hw_is_max
      have h2 : s_alpha_d {a := 2, b := 3} = m := h_uniq_eq _ h_max
      rw [h1, h2]
    rw [h_w_eq]
  · rintro rfl
    exact ⟨s_alpha_d {a := 2, b := 3}, h_max, rfl⟩

def cLength : D∞ → ℕ
  | r k => 2 * k.natAbs
  | sr k =>
    let ki : ℤ := k
    if ki > 0 then 2 * ki.natAbs - 1 else 2 * ki.natAbs + 1

@[simp]
lemma cLength_eq (g : D∞) : cLength g = ℓ g := by
  cases g with
  | r k => simp [cLength]
  | sr k => simp [cLength]

instance instDecidableLeDegree (d1 d2 : Degree) : Decidable (d1 ≤ d2) :=
  inferInstanceAs (Decidable (d1.a ≤ d2.a ∧ d1.b ≤ d2.b))

def enumerateD_list (n : ℕ) : List D∞ :=
  (List.range (n + 1)).flatMap fun k =>
    [cs.wordProd (alternatingWord 0 1 k), cs.wordProd (alternatingWord 1 0 k)]

def enumerateD (n : ℕ) : Finset D∞ :=
  (enumerateD_list n).toFinset

def Ad_finset (u : Vertex) (d : Degree) : Finset Vertex :=
  let limit := d.a + d.b + 1
  (enumerateD limit).filter (fun v => cLength (u * v) = cLength u + cLength v ∧ φ v ≤ d)

def CurveNeighborhood_computable (u : Vertex) (d : Degree) : Finset Vertex :=
  let A := Ad_finset u d
  let maxA := A.filter (fun w => ∀ w' ∈ A, ¬(cLength w < cLength w'))
  maxA.image (fun w => u * w)

instance : ToString (ZMod 0) := inferInstanceAs (ToString ℤ)

instance : Repr D∞ where
  reprPrec g _ :=
    match g with
    | r k => if k = 0 then "1" else s!"r({k})"
    | sr k => s!"sr({k})"

#eval CurveNeighborhood_computable 1 ⟨2, 2⟩
#eval CurveNeighborhood_computable s0 ⟨2, 3⟩
#eval CurveNeighborhood_computable s1 ⟨3, 3⟩
