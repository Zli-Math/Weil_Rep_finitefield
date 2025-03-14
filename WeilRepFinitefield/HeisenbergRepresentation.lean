import Mathlib
import WeilRepFinitefield.Quadratic

noncomputable section Schrodinger_Model_of_Heisenberg_Representation

open Heisenberg Function

variable {K : Type } [hfK : Field K] [Fintype K] {V : Type } [hcV : AddCommGroup V] [hmV : Module K V] [FiniteDimensional K V] (B : V → V → K) [IsBilinear B]

local notation "B_s" => (alternatingform B)

/- This definition is not correct
structure polarization (X Y: Submodule K V) where
dimX : Module.finrank K X * 2 = Module.finrank K V
dualXY : Y ≃ₗ[K] Module.Dual K X
mul_zero : ∀ x : X, ∀ y : Y,  B_s x.1 y.1 = 0
-/

#check Module.finrank_directSum

class polarization (X Y: Submodule K V) where
spanning : ∀ v : V, ∃! x: X, ∃! y :Y, v = x + y
Xisotropic : ∀ x y : X, B_s x y = 0
Yisotropic : ∀ x y : Y, B_s x y = 0

--variable  (X Y: Submodule K V) (x : X) (y : Y )

--#check (x+y : V)
/-
Establish the non-deg
-/

--χ₀ takes values in {1, -1}
variable {X Y : Submodule K V} (χ₀ : AddChar K ℂˣ) (hp : polarization B X Y)

variable (X) in
def subXK : @Subgroup (Heisenberg B) (Heisenberg.instGroup B) where
  carrier := by
    rw [Heisenberg]
    exact Set.prod X.carrier Set.univ
  mul_mem' := by
    intro x y h1 h2
    simp_all [Heisenberg.mul_def]
    constructor
    · rw [Set.prod] at h1 h2
      rw [Set.mem_def] at h1 h2
      simp [X.add_mem]
      exact Submodule.add_mem X h1.1 h2.1
    · simp
  one_mem' := by simp [Set.prod]
  inv_mem' := by
    intro x h
    simp [Set.prod, Heisenberg.inv_def]
    exact h.1


class extendcharacter (χ : (subXK B (X := X))→* ℂˣ) where
equalχ₀ : ∀ y, χ ⟨(0, y), by simp [subXK, Set.prod]⟩ = χ₀ y
--χ takes values in {1, -1, i, -i}

variable (χ : (subXK B (X := X)) →* ℂˣ) [isextendchara : extendcharacter B χ₀ χ] (x : X)

def Schrodinger_model := {f : Heisenberg B → ℂ | ∀ h : Heisenberg B, ∀ x: subXK B (X := X) ,f (h * x) = (χ x)⁻¹ * f (h)}

local notation "Sch" => Schrodinger_model B χ

namespace Schrodinger_model

omit [Fintype K] [FiniteDimensional K V] in
lemma ext (f g : Sch) : (∀ h, f.1 h = g.1 h) → f = g:= by
  intro h; ext; simp [h]

omit [Fintype K] [FiniteDimensional K V] in
lemma Sch_act_mem (h1 : f ∈ Sch)(h : Heisenberg B) : (fun g => f (h * g)) ∈ Sch := by
  intro h' x
  calc
  _ =  f (h * (h' *x)) := by rfl
  _ =  f ((h * h') *x) := by group
  _ = (χ x)⁻¹ * f (h * h') := h1 (h * h') x




lemma Sch_add_mem (h1 : f1 ∈  Schrodinger_model B χ) (h2 : f2 ∈ Schrodinger_model B χ): f1 + f2 ∈ Schrodinger_model B χ := by
  simp [Schrodinger_model]
  sorry

lemma Sch_zero_mem : 0 ∈ Schrodinger_model B χ := by sorry

lemma Sch_smul_mem (r : ℂ ) (f : Heisenberg B → ℂ): f ∈  Schrodinger_model B χ → r • f ∈  Schrodinger_model B χ := by sorry

noncomputable instance : Submodule ℂ (Heisenberg B → ℂ) where
  carrier := Schrodinger_model B χ
  add_mem' := Sch_add_mem B χ
  zero_mem' := Sch_zero_mem B χ
  smul_mem' := Sch_smul_mem B χ

noncomputable instance : AddCommMonoid (Schrodinger_model B χ) := Submodule.addCommMonoid (instSubmoduleComplexForallHeisenberg B χ)

noncomputable instance : AddCommGroup (Schrodinger_model B χ) := Submodule.addCommGroup (instSubmoduleComplexForallHeisenberg B χ)

noncomputable instance : Module ℂ (Schrodinger_model B χ) := Submodule.module (instSubmoduleComplexForallHeisenberg B χ)

noncomputable instance : Ring  (Module.End ℂ (Schrodinger_model B χ)):= inferInstance

abbrev rho_aux (h : Heisenberg B) : Module.End ℂ (Schrodinger_model B χ)
  where
  toFun := fun f => ⟨fun h2 => f.1 (h⁻¹ * h2), Sch_act_mem B χ f.2 h⁻¹⟩
  map_add' := by
    intro f1 f2
    apply ext; intro h'
    simp_all only
    obtain ⟨val_1, property_1⟩ := f1
    obtain ⟨val_2, property_2⟩ := f2
    obtain ⟨fst_1, snd_1⟩ := h'
    simp_all only
    rfl
  map_smul' := by
    intro m x_1
    simp_all only [RingHom.id_apply]
    obtain ⟨val_1, property_1⟩ := x_1
    simp_all only
    rfl



def rho : Heisenberg B  →* Module.End ℂ (Schrodinger_model B χ) where
  toFun := rho_aux B χ
  map_one' := sorry
  map_mul' := sorry

-- The GeneralLinearGroup packet in mathlib is not good, so choose not to define it as linearEquiv
--def rho : Heisenberg B  →* LinearMap.GeneralLinearGroup ℂ (Schrodinger_model B χ):= MonoidHom.toHomUnits (rho_aux1 B χ)

variable {B} in
abbrev Ymodel (hp: polarization B X Y):= Y → ℂ

variable {B} in
def homY (hp : polarization B X Y) : (Schrodinger_model B χ) ≃ₗ[ℂ] (Ymodel hp) where
  toFun := fun f => (fun y => f.1 y)
  map_add' := sorry
  map_smul' := sorry
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

variable {B} in
def rhoY : Heisenberg B →* Module.End ℂ (Ymodel hp) where
  toFun :=   (LinearEquiv.conj (homY χ hp)) ∘ (rho B χ)
  map_one' := sorry
  map_mul' := sorry

local notation "ρ" => (rhoY hp χ)

-- Lemma 2.3 correct the expression on RHS
lemma rhoY.eq (x : X) (y y': Y) (t:K) (f : Ymodel hp) : (rhoY hp χ) (⟨x+y,t⟩: Heisenberg B) f y'=  χ ⟨⟨x,t⟩,by sorry⟩ * f (y' - y):= by sorry


variable {B} in
def rhoY.map_mul (h h' : Heisenberg B):  ρ h * ρ h' =  ρ (h * h') := by simp only [_root_.map_mul]

end Schrodinger_model

end Schrodinger_Model_of_Heisenberg_Representation
