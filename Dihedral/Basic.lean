import Mathlib.GroupTheory.SpecificGroups.Dihedral

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.GroupTheory.Coxeter.Length

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.List.Basic

import Mathlib.Tactic

--无限二面体群由sr0、sr1生成
open DihedralGroup CoxeterSystem List

notation "D∞" => DihedralGroup 0

lemma r1_in_D :
  r (1 : ZMod 0) ∈ (Subgroup.closure ({sr (0 : ZMod 0), sr (1)} : Set (DihedralGroup 0))) := by
  have h_r1 : r (1 : ZMod 0) = sr 0 * sr 1 := by simp only [sr_mul_sr, sub_zero]
  rw [h_r1]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
      (Subgroup.subset_closure (Set.mem_insert_of_mem (sr 0) rfl))

lemma r_zpow_in_D : ∀ k : ℤ, r (k : ZMod 0) ∈ (Subgroup.closure ({sr (0 : ZMod 0),
  sr (1 : ZMod 0)} : Set (DihedralGroup 0))) := by
  intro k
  have h : (r (1 : ZMod 0)) ^ (k : _) = r (k : ZMod 0) := by simp only [r_zpow, one_mul, r.injEq]; rfl
  rw [← h]
  exact Subgroup.zpow_mem _ r1_in_D (k : _)

lemma sri_in_D : ∀ i : ZMod 0, sr i ∈ (Subgroup.closure ({sr (0 : ZMod 0),
  sr (1 : ZMod 0)} : Set (DihedralGroup 0))) := by
  intro i
  have h : sr (0 : ZMod 0) * r (i : ZMod 0) = sr i := by simp only [sr_mul_r, zero_add]
  rw [← h]
  exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) (r_zpow_in_D (i : ℤ))

theorem gen_by_sr0_sr1 :
  (Subgroup.closure ({sr (0 : ZMod 0), sr (1 : ZMod 0)} : Set (DihedralGroup 0))) = ⊤ := by
  rw [eq_top_iff]
  rintro (a | b) -
  · exact r_zpow_in_D (a : ℤ)
  · exact sri_in_D b

def s0 : D∞ := sr (0 : ZMod 0)
def s1 : D∞ := sr (1 : ZMod 0)

def B : Type := Fin 2
def M : CoxeterMatrix (Fin 2) :={
  M := !![1, 0; 0, 1]
  isSymm := by decide
  diagonal := by decide
  off_diagonal := by decide
}

def f : Fin 2 → D∞ := ![s0, s1]

lemma f_sq_one (i : Fin 2) : (f i) * (f i) = 1 := by
  fin_cases i <;> decide

lemma f_is_liftable : M.IsLiftable f := by
  intro i j
  simp only [M, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one]
  fin_cases i <;> fin_cases j <;> decide

def φ : M.Group →* D∞ := (M.toCoxeterSystem).lift ⟨f, f_is_liftable⟩

def s0m := M.simple (0 : Fin 2)
def s1m := M.simple (1 : Fin 2)
def cs' := M.toCoxeterSystem

lemma conj_eq_inv {z : ℤ} : s0m * (s0m * s1m)^ z * s0m =( (s0m * s1m)⁻¹)^ z := by
  have e0 : s0m * s0m = 1 := cs'.simple_sq (0 : Fin 2)
  have e1 : s1m * s1m = 1 := cs'.simple_sq (1 : Fin 2)
  have hs0 : s0m⁻¹ = s0m := inv_eq_of_mul_eq_one_right e0
  have hs1 : s1m⁻¹ = s1m := inv_eq_of_mul_eq_one_right e1
  have h1 : s0m * (s0m * s1m) * s0m⁻¹ = (s0m * s1m)⁻¹ := by
    rw [hs0, mul_inv_rev, hs0, hs1, ← mul_assoc, e0, one_mul]
  rw [← h1, conj_zpow, hs0]

def ψ : D∞ →* M.Group where
  toFun x := match x with
    | DihedralGroup.r i => (s0m * s1m) ^ (i.cast : ℤ)
    | DihedralGroup.sr i => s0m * (s0m * s1m) ^ (i.cast : ℤ)
  map_one' := by
    rw [show (1 : D∞) = r (0 : ZMod 0) by rfl]
    simp only [ZMod.cast_zero, zpow_zero]
  map_mul' := by
    rintro (a | a) (b | b)
    all_goals simp; group
    · calc s0m * (s0m * s1m) ^ ((b.cast : ℤ) - a.cast)
        _ =s0m * (s0m * s1m) ^ ((b.cast : ℤ) - a.cast) * 1 := by rw [mul_one]
        _ =s0m * (s0m * s1m) ^ ((b.cast : ℤ) - a.cast) * (s0m * s0m) := by
          congr; symm ;exact cs'.simple_sq (0 : Fin 2)
        _ =(s0m * (s0m * s1m) ^ ((b.cast : ℤ) - a.cast) * s0m) *s0m := by group
        _ =((s0m * s1m)⁻¹ ^ (((b.cast : ℤ) - a.cast))) * s0m := by rw [conj_eq_inv]
        _ =(s0m * s1m) ^ (a.cast : ℤ) * (s0m * s1m)⁻¹ ^ (b.cast : ℤ) * s0m := by
          rw [inv_zpow, ←zpow_neg, neg_sub, zpow_sub, inv_zpow]
        _ =(s0m * s1m) ^ (a.cast : ℤ) *s0m * (s0m * s1m)^ (b.cast : ℤ) * (s0m * s0m) := by
          rw [←conj_eq_inv];group
        _ =(s0m * s1m) ^ (a.cast : ℤ) * s0m * (s0m * s1m) ^ (b.cast : ℤ) := by
          rw [show s0m *s0m = 1 by exact cs'.simple_sq (0 : Fin 2), mul_one]
    · rw [conj_eq_inv, inv_zpow, ←zpow_neg, ← zpow_add, add_comm]
      rfl

def mulEquiv : D∞ ≃* M.Group where
  toFun := ψ.toFun
  invFun := φ.toFun
  left_inv := by
    intro x
    cases x with
    | r i =>
      dsimp [ψ]
      have : φ ((s0m * s1m) ^ (i.cast : ℤ)) = (f 0 * f 1) ^ (i.cast : ℤ) := by simp; congr
      rw [this, f, s0, s1]
      simp
    | sr i =>
      simp only [ψ, OneHom.toFun_eq_coe, OneHom.coe_mk, MonoidHom.toOneHom_coe, map_mul, map_zpow]
      rw [show φ (s0m) = f 0 by rfl, show φ (s1m) = f 1 by rfl]
      dsimp [f]
      rw [show (s0 * s1) = r 1 by rfl, show s0 = sr (0 : ZMod 0) by rfl]
      simp
  right_inv := by
    have h : (ψ.comp φ) = {
        toFun := fun x => x
        map_one' := by simp
        map_mul' := by intros; simp } := by
      apply (M.toCoxeterSystem).ext_simple
      intro i
      simp only [MonoidHom.comp_apply]
      have hφ := (M.toCoxeterSystem).lift_apply_simple (f_is_liftable) i
      fin_cases i
      all_goals
        dsimp [ψ]
        simp_all only [Fin.zero_eta, Fin.isValue, CoxeterMatrix.toCoxeterSystem_simple]
      · rfl
      · dsimp [φ] at *
        rw [hφ, f, s1]
        simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one, dvd_refl,
          ZMod.cast_one, zpow_one]
        group
        change M.simple 0 ^2 * M.simple 1 = M.simple 1
        simp only [Fin.isValue, mul_eq_right]
        exact (M.toCoxeterSystem).simple_sq (0 : Fin 2)
    intro g
    exact congrArg (fun m => m.toFun g) h
  map_mul' := by exact ψ.map_mul'

def cs : CoxeterSystem M D∞ := { mulEquiv := mulEquiv}

notation "ℓ" => cs.length

lemma s0' : s0 = cs.simple 0 := rfl
lemma s1' : s1 = cs.simple 1 := rfl

