import Dihedral.Ad

open CoxeterSystem DihedralGroup Nat

@[simp] private lemma Degree.add_a (d e : Degree) : (d + e).a = d.a + e.a := rfl

@[simp] private lemma Degree.add_b (d e : Degree) : (d + e).b = d.b + e.b := rfl

/-- The maximal positive root bounded by a degree, written `α(d)` in the paper. -/
def root_from_degree (d : Degree) : Root :=
  if d.a > d.b then
    ⟨d.b + 1, d.b, Or.inl rfl⟩
  else
    ⟨d.a, d.a + 1, Or.inr rfl⟩

/-- Semantic name for the paper's maximal root `α(d)`. -/
def maxRootLE (d : Degree) : Root := root_from_degree d

/-- The root reflection `s_{α(d)}` attached to the maximal root below `d`. -/
def s_alpha_d (d : Degree) : Vertex := s_α (root_from_degree d)

/-- Semantic name for the root reflection `s_{α(d)}`. -/
def rootReflectionLE (d : Degree) : Vertex := s_alpha_d d

def s0s1_pow (a : ℕ) : Vertex := cs.wordProd (alternatingWord 0 1 (2 * a))
def s1s0_pow (a : ℕ) : Vertex := cs.wordProd (alternatingWord 1 0 (2 * a))

lemma s0s1_pow_equiv (a : ℕ) : s0s1_pow a = r (a : ℤ) := by
  simp only [s0s1_pow, Fin.isValue]
  rw [cs.prod_alternatingWord_eq_mul_pow 0 1]
  simp [s0, s1, sr_mul_sr, ← s0', ← s1']
  rfl

lemma s1s0_pow_equiv (a : ℕ) : s1s0_pow a = r (-(a : ℤ)) := by
  simp only [s1s0_pow, Fin.isValue]
  rw [cs.prod_alternatingWord_eq_mul_pow 1 0]
  simp [s0, s1, sr_mul_sr, ← s0', ← s1']
  rfl

lemma phi_sr0_add_phi_sr_eq_phi_r_pos (k : ℤ) (hk : 0 < k) :
    φ (sr (0 : ℤ)) + φ (sr k) = φ (r k) := by
  ext
  all_goals
    simp [getDegree_sr, getDegree_r] <;> omega

lemma phi_sr1_add_phi_sr_succ_eq_phi_r_neg (k : ℤ) (hk : k < 0) :
    φ (sr (1 : ℤ)) + φ (sr ((k + 1 : ℤ))) = φ (r k) := by
  have h_abs_step : (k + 1).natAbs + 1 = k.natAbs := by omega
  ext
  all_goals
    simp [getDegree_sr, getDegree_r] <;> omega

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
    simp [hαk, sr_mul_sr]
    exact (sub_zero (k : ZMod 0)).symm
  have h_chaink : HasChain 1 (r k) (φ (sr (0 : ℤ)) + αk.toDegree) :=
    HasChain.step h_chain0 h_edgek
  have h_degk : αk.toDegree = φ (sr k) := by
    rw [← hαk]
    simpa using (φ_s_alpha_eq αk).symm
  rw [h_degk] at h_chaink
  rw [phi_sr0_add_phi_sr_eq_phi_r_pos k hk] at h_chaink
  exact h_chaink

lemma trivial_chain_r_neg (k : ℤ) (hk : k < 0) : HasChain 1 (r k) (φ (r k)) := by
  obtain ⟨αk1, hαk1⟩ := exists_root_eq_sr (k + 1 : ℤ)
  have h_chain1 : HasChain 1 (sr (1 : ℤ)) (φ (sr (1 : ℤ))) := trivial_chain_sr 1
  have h_edgek1 : IsEdge (sr (1 : ℤ)) (r k) αk1 := by
    dsimp [IsEdge]
    rw [hαk1, sr_mul_sr]
    apply congrArg r
    change (k : ZMod 0) = ((k + 1 : ℤ) : ZMod 0) - 1
    norm_num
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
      change HasChain 1 (r (0 : ZMod 0)) (φ (r (0 : ZMod 0)))
      rw [show r (0 : ZMod 0) = (1 : Vertex) by rfl]
      change HasChain 1 1 (0 : Degree)
      exact HasChain.refl 1
    · by_cases hk_pos : 0 < k'
      · simpa [k'] using trivial_chain_r_pos k' hk_pos
      · have hk_neg : k' < 0 := by omega
        simpa [k'] using trivial_chain_r_neg k' hk_neg

/-- Paper Theorem 3.3, first reduction: the identity curve neighborhood is
exactly the maximal-element set of `A_d(1)`. -/
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
      have h_phi_le_d' := inv_mul_degree_le_of_chain 1 v d' h_chain
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
        have h_phi_le_d' := inv_mul_degree_le_of_chain 1 x d' h_chain
        simp only [inv_one, one_mul] at h_phi_le_d'
        exact le_trans h_phi_le_d' h_d'_le_d
      apply h_in_Ad.2 x h_x_in_Ad h_v_lt_x

/-- Formula (3), diagonal case: at the identity a diagonal degree has two maximal endpoints. -/
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

/-- Formula (3), off-diagonal maximality: `s_{α(d)}` is the unique maximal
endpoint of `A_d(1)` when `d` is not diagonal. -/
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
      rfl
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
      rfl
    rw [hs, ad_one_eq_degree_le]
    refine ⟨?_, ?_⟩
    · simp [getDegree_sr]
      omega
    · intro (v : D∞) hv hv_le
      have hv_cmp : (ℓ (sr (((d.a : ℤ) + 1 : ℤ))) < ℓ v) ∨
          (sr (((d.a : ℤ) + 1 : ℤ)) = v) := by
        rcases hv_le with hlt | heq
        · left
          exact (lt_iff_length_lt _ _).mp hlt
        · right
          exact heq
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
        · exact heq

/-- Formula (3), off-diagonal case, using the historical name `s_alpha_d`. -/
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

/-- Formula (3), off-diagonal case, using the semantic name `rootReflectionLE`. -/
theorem curve_nbhd_one_offdiag_rootReflectionLE (d : Degree) (p : d.a ≠ d.b) :
    CurveNeighborhood 1 d = { rootReflectionLE d } := by
  simpa [rootReflectionLE] using curve_nbhd_one_offdiag d p

/-- Complete identity-neighborhood classification, matching paper formula (3). -/
theorem curve_nbhd_one (d : Degree) :
    CurveNeighborhood 1 d =
      if d.a = d.b then
        { s0s1_pow d.a, s1s0_pow d.a }
      else
        { s_alpha_d d } := by
        split_ifs with h
        · exact curve_nbhd_one_diag d h
        · exact curve_nbhd_one_offdiag d h
