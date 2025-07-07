import Mathlib
--import WeilRepFinitefield.Quadratic
import Mathlib.Heisenberg

noncomputable section Schrodinger_Model

open Heisenberg Function


namespace  Schrodinger_Model

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
spanning : ∀ v : V, ∃! (w : (X × Y)), v = w.1 + w.2
Xisotropic : ∀ x y : X, B_s x y = 0
Yisotropic : ∀ x y : Y, B_s x y = 0
XY_directsum : ∀ x : X, ∀ y : Y, B_s x y = 0
YX_directsum : ∀ y : Y, ∀ x : X, B_s y x = 0

/-
variable  (X Y: Submodule K V) (x : X) (y : Y )

#check (x+y : V)
-/
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


def X_coor (w : Heisenberg B) : X := ((hp.1 w.1).choose).1
def Y_coor (w : Heisenberg B) : Y := ((hp.1 w.1).choose).2


omit [Fintype K] [FiniteDimensional K V] [IsBilinear B] in
lemma element_XY : ∀ w : Heisenberg B, w = ((X_coor B hp w).1 + (Y_coor B hp w).1, w.2):= by
  intro w
  ext
  · simp [X_coor, Y_coor]
    have := (Classical.choose_spec (hp.1 w.1)).1
    simp at this
    exact this
  · simp

omit [Fintype K] [FiniteDimensional K V] [IsBilinear B] in
lemma element_of_V_XY : ∀ w : V, w = (X_coor B hp w).1 + (Y_coor B hp w).1:= by
  intro w
  simp [X_coor, Y_coor]
  have := (Classical.choose_spec (hp.1 w)).1
  simp at this
  exact this


omit [Fintype K] [FiniteDimensional K V] [IsBilinear B] in
lemma coor_linear : ∀ w v, w * v =  ((X_coor B hp w).1 + (Y_coor B hp w).1 + ((X_coor B hp v).1 + (Y_coor B hp v).1), w.2 + v.2 + B w.1 v.1 ) := by
  intro w v
  simp [Heisenberg.mul_def]
  have hw := element_XY B hp w
  have hv := element_XY B hp v
  nth_rw 1 [hw, hv]

omit [Fintype K] [FiniteDimensional K V] [IsBilinear B] in
lemma XY_coor_linear : ∀ w v, (X_coor B hp (w * v)).1 = (X_coor B hp w).1 + (X_coor B hp v).1 ∧ (Y_coor B hp (w * v)).1 = (Y_coor B hp w).1 + (Y_coor B hp v).1 := by
  intro w v
  have hwv := coor_linear B hp w v
  have hwv1 : (w * v).1 = ((X_coor B hp w).1 + ((X_coor B hp v).1) + ((Y_coor B hp w).1  + (Y_coor B hp v).1)) := by
    simp [hwv]
    rw [add_assoc, ← add_assoc (Y_coor B hp w).1, add_comm  (Y_coor B hp w).1, add_assoc (X_coor B hp v).1, ← add_assoc]
  have hwv2 := (Exists.choose_spec (hp.1 (w * v).1))
  simp at hwv2
  have hX : ((X_coor B hp w).1 + ((X_coor B hp v).1) : V) ∈ X := by
    norm_cast
    simp [Submodule.add_mem]
  rcases hwv2 with ⟨h1, h2⟩
  have hY : ((Y_coor B hp w).1 + ((Y_coor B hp v).1) : V) ∈ Y := by
    norm_cast
    simp [Submodule.add_mem]
  have h := h2 ((X_coor B hp w).1 + ((X_coor B hp v).1) : V) hX ((Y_coor B hp w).1 + ((Y_coor B hp v).1) : V) hY hwv1
  have h' := element_XY B hp (w * v)
  have h'' : (w * v).1 = (X_coor B hp (w * v)).1 + (Y_coor B hp (w * v)).1 := by nth_rw 1 [h']
  simp [X_coor, Y_coor]
  rw [← h]
  simp [X_coor, Y_coor]


omit [Fintype K] [FiniteDimensional K V] [IsBilinear B] in
lemma X_in_X (w : V) (t : K) (h : w ∈ X) : X_coor B hp (w, t) = w := by
  simp [X_coor]
  have h0 : (0 : V) ∈ Y := by simp
  have hw := (Exists.choose_spec (hp.1 w))
  simp at hw
  rcases hw with ⟨h1, h2⟩
  have hw := h2 w h 0 h0 (by simp)
  rw [← hw]

omit [Fintype K] [FiniteDimensional K V] [IsBilinear B] in
lemma Y_in_Y (w : V) (t : K) (h : w ∈ Y) : Y_coor B hp (w, t) = w := by
  simp [Y_coor]
  have h0 : (0 : V) ∈ X := by simp
  have hw := (Exists.choose_spec (hp.1 w))
  simp at hw
  rcases hw with ⟨h1, h2⟩
  have hw := h2 0 h0 w h (by simp)
  rw [← hw]

omit [Fintype K] [FiniteDimensional K V] [IsBilinear B] in
lemma X_coor_of_Y (y : V) (t : K) (h : y ∈ Y) : X_coor B hp (y, t) = 0 := by
  have hx := element_XY B hp (y, 0)
  have hx':= Y_in_Y B hp y 0 h
  rw [hx'] at hx
  simp at hx
  exact hx

omit [Fintype K] [FiniteDimensional K V] in
lemma X_coor_add_Y (w : V) (t : K) (x : V) (h : x ∈ Y) : X_coor B hp (w+x,t) = X_coor B hp (w,t) := by
  have : (w + x, t) = (w , t - B w x) * ((x, 0) : Heisenberg B) := by simp [Heisenberg.mul_def]
  rw [this]
  have := (XY_coor_linear B hp (w, t - B w x) (x, 0)).1
  norm_cast at this
  rw [this]
  rw [X_coor_of_Y B hp x 0 h]
  simp_all [X_coor]


omit [Fintype K] [FiniteDimensional K V] [IsBilinear B] in
lemma Y_coor_of_X (x : V) (t : K) (h : x ∈ X) : Y_coor B hp (x, t) = 0 := by
  have hx := element_XY B hp (x, 0)
  have hx':= X_in_X B hp x 0 h
  rw [hx'] at hx
  simp at hx
  exact hx


omit [Fintype K] [FiniteDimensional K V] in
lemma Y_coor_add_X (w : V) (t : K) (x : V) (h : x ∈ X) : Y_coor B hp (w+x,t) = Y_coor B hp (w,t) := by
  have : (w + x, t) = (w , t - B w x) * ((x, 0) : Heisenberg B) :=by    simp [Heisenberg.mul_def]
  rw [this]
  have := (XY_coor_linear B hp (w, t - B w x) (x, 0)).2
  norm_cast at this
  rw [this]
  rw [Y_coor_of_X B hp x 0 h]
  simp_all [Y_coor]


omit [Fintype K] [FiniteDimensional K V] in
lemma element_XY' : ∀ w : Heisenberg B, w = ((Y_coor B hp w).1, 0) *(((X_coor B hp w).1, w.2 - B  (Y_coor B hp w).1 (X_coor B hp w).1)) := by
  intro w
  simp [Heisenberg.mul_def]
  rw [add_comm]
  exact element_XY B hp w

omit [Fintype K] [FiniteDimensional K V] in
lemma Y_coor_add_Y (w : V) (t : K) (y : Y) : Y_coor B hp (w + y, t) = Y_coor B hp (w, t) + y := by
  have : (w + y, t) = (w , t - B w y) * ((y, 0) : Heisenberg B) :=by    simp [Heisenberg.mul_def]
  rw [this]
  have := (XY_coor_linear B hp (w, t - B w y) (y,0)).2
  norm_cast at this
  rw [this]
  have := Y_in_Y B hp y 0 (by simp)
  norm_cast at this
  rw [this]
  simp [Y_coor]

omit [Fintype K] [FiniteDimensional K V] [IsBilinear B] in
lemma XY_coor (w : V) (t : K) : X_coor B hp (w, t) = X_coor B hp w ∧   Y_coor B hp (w, t) = Y_coor B hp w := by simp [X_coor, Y_coor]

omit [Fintype K] [FiniteDimensional K V] in
lemma XY_coor_linear' (w : V) (v : V) : (X_coor B hp (w + v, 0) : V)= X_coor B hp w + X_coor B hp v ∧ (Y_coor B hp (w + v, 0) : V) = Y_coor B hp w + Y_coor B hp v := by
  have : (w + v, 0)= (w , - B w v) * ((v, 0) : Heisenberg B) :=by    simp [Heisenberg.mul_def]
  simp [this]
  have := XY_coor_linear B hp (w, -B w v) (v, 0)
  exact this




class extendcharacter (χ : (subXK B (X := X))→* ℂˣ) where
equalχ₀ : ∀ y, χ ⟨(0, y), by simp [subXK, Set.prod]⟩ = χ₀ y
--χ takes values in {1, -1, i, -i}

variable (χ : (subXK B (X := X)) →* ℂˣ) [isextendchara : extendcharacter B χ₀ χ] (x : X)

def Schrodinger_model := {f : Heisenberg B → ℂ | ∀ h : Heisenberg B, ∀ x: subXK B (X := X) ,f (h * x) = (χ x)⁻¹ * f (h)}

local notation "Sch" => Schrodinger_model B χ

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



omit [Fintype K] [FiniteDimensional K V] in
lemma Sch_add_mem (h1 : f1 ∈  Schrodinger_model B χ) (h2 : f2 ∈ Schrodinger_model B χ): f1 + f2 ∈ Schrodinger_model B χ := by
  simp_all [Schrodinger_model]
  intro a b x y hxy
  rw [← mul_add]

omit [Fintype K] [FiniteDimensional K V] in
lemma Sch_zero_mem : 0 ∈ Schrodinger_model B χ := by simp [Schrodinger_model]

omit [Fintype K] [FiniteDimensional K V] in
lemma Sch_smul_mem (r : ℂ ) (f : Heisenberg B → ℂ): f ∈  Schrodinger_model B χ → r • f ∈  Schrodinger_model B χ := by
  intro hf
  simp_all [Schrodinger_model]
  intro a b x y hxy
  simp [mul_assoc, mul_comm]

noncomputable instance : Submodule ℂ (Heisenberg B → ℂ) where
  carrier := Schrodinger_model B χ
  add_mem' := Sch_add_mem B χ
  zero_mem' := Sch_zero_mem B χ
  smul_mem' := Sch_smul_mem B χ

noncomputable instance : AddCommMonoid (Schrodinger_model B χ) := Submodule.addCommMonoid (instSubmoduleComplexForallHeisenberg B χ)

noncomputable instance : AddCommGroup (Schrodinger_model B χ) := Submodule.addCommGroup (instSubmoduleComplexForallHeisenberg B χ)

noncomputable instance : Module ℂ (Schrodinger_model B χ) := Submodule.module (instSubmoduleComplexForallHeisenberg B χ)

noncomputable instance : Ring  (Module.End ℂ (Schrodinger_model B χ)):= inferInstance

end Schrodinger_Model
end Schrodinger_Model
