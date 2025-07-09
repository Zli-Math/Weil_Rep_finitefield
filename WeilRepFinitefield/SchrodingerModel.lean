import Mathlib
--import WeilRepFinitefield.Quadratic
import WeilRepFinitefield.Heisenberg

noncomputable section Schrodinger_Model

open Function
open LinearMap.BilinForm


namespace  Schrodinger_Model

variable {K : Type } [hfK : Field K]  {V : Type } [hcV : AddCommGroup V] [hmV : Module K V]
(B : LinearMap.BilinForm K V)

local notation "B_s" => (B.toAlt)

/- This definition is not correct
structure polarization (X Y: Submodule K V) where
dimX : Module.finrank K X * 2 = Module.finrank K V
dualXY : Y ≃ₗ[K] Module.Dual K X
mul_zero : ∀ x : X, ∀ y : Y,  B_s x.1 y.1 = 0
-/

#check Module.finrank_directSum

variable {X Y : Submodule K V} (hp : B.Polarization X Y)
variable {R : Type*} [Field R]

variable  (χ₀ : AddChar K R)

class extendcharacter (χ : (B.toSubgroup X)→* Rˣ) where
  equalχ₀ : ∀ y, χ ⟨(0, y), by simp [LinearMap.BilinForm.Heisenberg,LinearMap.BilinForm.toSubgroup,Set.prod] ⟩ = χ₀ y
--χ takes values in {1, -1, i, -i}

variable (χ : (B.toSubgroup X) →* Rˣ) [isextendchara : extendcharacter B χ₀ χ] (x : X)

def Schrodinger_model := {f : B.Heisenberg → R | ∀ h : B.Heisenberg, ∀ x: B.toSubgroup X ,f (h * x) = (χ x)⁻¹ * f (h)}

local notation "Sch" => Schrodinger_model B χ

lemma ext (f g : Sch) : (∀ h, f.1 h = g.1 h) → f = g:= by
  intro h; ext; simp [h]

lemma Sch_act_mem (h1 : f ∈ Sch)(h : B.Heisenberg) : (fun g => f (h * g)) ∈ Sch := by
  intro h' x
  calc
  _ =  f (h * (h' *x)) := by rfl
  _ =  f ((h * h') *x) := by group
  _ = (χ x)⁻¹ * f (h * h') := h1 (h * h') x

lemma Sch_add_mem (h1 : f1 ∈  Schrodinger_model B χ) (h2 : f2 ∈ Schrodinger_model B χ): f1 + f2 ∈ Schrodinger_model B χ := by
  simp_all [Heisenberg,Schrodinger_model]
  intro a b x y hxy
  rw [← mul_add]

lemma Sch_zero_mem : 0 ∈ Schrodinger_model B χ := by simp [Schrodinger_model]

lemma Sch_smul_mem (r : R ) (f : B.Heisenberg → R): f ∈  Schrodinger_model B χ → r • f ∈  Schrodinger_model B χ := by
  intro hf
  simp_all [Heisenberg,Schrodinger_model]
  intro a b x y hxy
  simp [mul_assoc, mul_comm]

instance instSubmodule: Submodule R (B.Heisenberg → R) where
  carrier := Schrodinger_model B χ
  add_mem' := Sch_add_mem B χ
  zero_mem' := Sch_zero_mem B χ
  smul_mem' := Sch_smul_mem B χ

instance instAddCommMonoid: AddCommMonoid (Schrodinger_model B χ) := Submodule.addCommMonoid (instSubmodule B χ)

instance : AddCommGroup (Schrodinger_model B χ) := Submodule.addCommGroup (instSubmodule B χ)

instance : Module R (Schrodinger_model B χ) := Submodule.module (instSubmodule B χ)

instance : Ring  (Module.End R (Schrodinger_model B χ)):= inferInstance

end Schrodinger_Model
end Schrodinger_Model
