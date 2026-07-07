import Dihedral.CurveNeighborhood

open DihedralGroup CoxeterSystem

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

lemma wordProd_alternating_mem_enumerateD {i j : Fin 2} {m n : ℕ}
    (hij : i ≠ j) (hmn : m ≤ n) :
    cs.wordProd (alternatingWord i j m) ∈ enumerateD n := by
  dsimp [enumerateD, enumerateD_list]
  simp only [List.mem_toFinset, List.mem_flatMap, List.mem_range, List.mem_cons]
  use m
  constructor
  · omega
  · fin_cases i <;> fin_cases j <;> simp_all

lemma mem_enumerateD_of_length_le {g : D∞} {n : ℕ} (hg : ℓ g ≤ n) :
    g ∈ enumerateD n := by
  induction g using alternating_cases with
  | h i j m hij =>
      rw [length_wordprod m hij] at hg
      exact wordProd_alternating_mem_enumerateD hij hg

def Ad_finset (u : Vertex) (d : Degree) : Finset Vertex :=
  let limit := d.a + d.b + 1
  (enumerateD limit).filter (fun v => cLength (u * v) = cLength u + cLength v ∧ φ v ≤ d)

lemma mem_Ad_of_mem_Ad_finset {u : Vertex} {d : Degree} {v : Vertex}
    (hv : v ∈ Ad_finset u d) : v ∈ Ad u d := by
  dsimp [Ad_finset] at hv
  simp only [Finset.mem_filter] at hv
  exact ⟨by simpa [cLength_eq] using hv.2.1, hv.2.2⟩

lemma mem_Ad_finset_iff {u : Vertex} {d : Degree} {v : Vertex} :
    v ∈ Ad_finset u d ↔ v ∈ Ad u d := by
  constructor
  · exact mem_Ad_of_mem_Ad_finset
  · intro hv
    dsimp [Ad_finset]
    simp only [Finset.mem_filter]
    constructor
    · exact mem_enumerateD_of_length_le (ad_length_bound v hv)
    · exact ⟨by simpa [cLength_eq] using hv.1, hv.2⟩

@[simp]
theorem coe_Ad_finset (u : Vertex) (d : Degree) :
    (Ad_finset u d : Set Vertex) = Ad u d := by
  ext v
  exact mem_Ad_finset_iff

def CurveNeighborhood_computable (u : Vertex) (d : Degree) : Finset Vertex :=
  let A := Ad_finset u d
  let maxA := A.filter (fun w => ∀ w' ∈ A, ¬(cLength w < cLength w'))
  maxA.image (fun w => u * w)

lemma exists_ad_of_mem_curveNeighborhood_computable {u : Vertex} {d : Degree} {v : Vertex}
    (hv : v ∈ CurveNeighborhood_computable u d) :
    ∃ w, w ∈ Ad u d ∧ v = u * w := by
  dsimp [CurveNeighborhood_computable] at hv
  rcases Finset.mem_image.mp hv with ⟨w, hw, h_eq⟩
  exact ⟨w, mem_Ad_of_mem_Ad_finset (Finset.mem_filter.mp hw).1, h_eq.symm⟩

lemma exists_maximal_ad_of_mem_curveNeighborhood_computable {u : Vertex} {d : Degree} {v : Vertex}
    (hv : v ∈ CurveNeighborhood_computable u d) :
    ∃ w, IsMaximalIn w (Ad u d) ∧ v = u * w := by
  dsimp [CurveNeighborhood_computable] at hv
  rcases Finset.mem_image.mp hv with ⟨w, hw, h_eq⟩
  rcases Finset.mem_filter.mp hw with ⟨hw_ad_finset, hw_max⟩
  refine ⟨w, ?_, h_eq.symm⟩
  constructor
  · exact mem_Ad_finset_iff.mp hw_ad_finset
  · intro w' hw'_ad hle
    by_contra hne
    have hlt : w < w' := lt_of_le_of_ne hle hne
    rw [lt_iff_length_lt] at hlt
    have hmax := hw_max w' (mem_Ad_finset_iff.mpr hw'_ad)
    exact hmax (by simpa [cLength_eq] using hlt)

theorem mem_CurveNeighborhood_computable_iff {u : Vertex} {d : Degree} {v : Vertex} :
    v ∈ CurveNeighborhood_computable u d ↔ v ∈ CurveNeighborhood u d := by
  constructor
  · intro hv
    rw [curve_nbhd_eq_mul_max_ad]
    exact exists_maximal_ad_of_mem_curveNeighborhood_computable hv
  · intro hv
    rw [curve_nbhd_eq_mul_max_ad] at hv
    rcases hv with ⟨w, hw_max, rfl⟩
    dsimp [CurveNeighborhood_computable]
    apply Finset.mem_image.mpr
    refine ⟨w, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    constructor
    · exact mem_Ad_finset_iff.mpr hw_max.1
    · intro w' hw'_finset hlen_lt
      have hw'_ad : w' ∈ Ad u d := mem_Ad_finset_iff.mp hw'_finset
      have hlt_order : w < w' := by
        rw [lt_iff_length_lt]
        simpa [cLength_eq] using hlen_lt
      have heq := hw_max.2 w' hw'_ad (le_of_lt hlt_order)
      have hlen_eq : cLength w = cLength w' := by rw [heq]
      exact (not_lt_of_ge (le_of_eq hlen_eq.symm)) hlen_lt

@[simp]
theorem coe_CurveNeighborhood_computable (u : Vertex) (d : Degree) :
    (CurveNeighborhood_computable u d : Set Vertex) = CurveNeighborhood u d := by
  ext v
  exact mem_CurveNeighborhood_computable_iff

/-!
The finite bound used by `Ad_finset` is `d.a + d.b + 1`, matching
`ad_length_bound`.
-/

instance : ToString (ZMod 0) := inferInstanceAs (ToString ℤ)

instance : Repr D∞ where
  reprPrec g _ :=
    match g with
    | r k => if k = 0 then "1" else s!"r({k})"
    | sr k => s!"sr({k})"

