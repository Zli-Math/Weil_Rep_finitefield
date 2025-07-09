import Mathlib
import WeilRepFinitefield.Compute

--import WeilRepFinitefield.Quadratic

section Symplectic_Group

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

variable (B : LinearMap.BilinForm K V) --[hnd : NonDegenerate (alternatingform B)]
--(nondegenerate_symplectic_form : nondegenerate (alternatingform B))

open Function

abbrev LinearMap.BilinForm.isAlt (B : LinearMap.BilinForm K V) (σ : V ≃ₗ[K] V) : Prop := ∀ w v, B (σ w) (σ v) - B w v = B (σ v) (σ w) - B v w

abbrev LinearMap.BilinForm.Sp := {σ : V ≃ₗ[K] V // B.isAlt σ }

namespace LinearMap.BilinForm.Sp



variable (σ : B.Sp)
variable {B}

lemma coe_map : σ.1 v  = σ v := rfl
lemma coe_map' : σ v  = σ.1 v := rfl


lemma preserveB : ∀ w v, B (σ w) (σ  v) - B w v = B (σ v) (σ w) - B v w := σ.2

lemma linear : ∀ w v, σ (w + v) = σ w + σ v := by
  simp only [coe_map', map_add, implies_true]

lemma slinear : ∀ (r : K) w, σ (r • w) = r • σ w := by
  intro r w
  simp only [coe_map', map_smul]

/-
lemma sym_auto_comp (σ₁ σ₂ : B.Sp) : ∀ w v, B ((σ₁ ∘ σ₂) w) ((σ₁ ∘ σ₂) v) - B w v = B ((σ₁ ∘ σ₂) v) ((σ₁ ∘ σ₂) w) - B v w := by
  intro w v
  simp [Function.comp,coe_map']
  have h₁ : B (σ₁ (σ₂ w)) (σ₁.1 (σ₂ v)) - B (σ₂ w) (σ₂ v) = B (σ₁ (σ₂ v)) (σ₁ (σ₂ w)) - B (σ₂ v) (σ₂ w) := σ₁.preserveB (σ₂ w) (σ₂ v)
  have h₂ : B (σ₂ w) (σ₂ v) - B w v = B (σ₂ v) (σ₂ w) - B v w := σ₂.2 w v
  linear_combination h₁ + h₂

-/

instance instFact_isALtclosed : Fact (∀ {a b}, B.isAlt a → B.isAlt b → B.isAlt (b.trans a)) where
  out :=  by
    intro σ₁ σ₂ p1 p2 w v
    have h₁ : B (σ₁ (σ₂ w)) (σ₁.1 (σ₂ v)) - B (σ₂ w) (σ₂ v) = B (σ₁ (σ₂ v)) (σ₁ (σ₂ w)) - B (σ₂ v) (σ₂ w) := p1 (σ₂ w) (σ₂ v)
    have h₂ : B (σ₂ w) (σ₂ v) - B w v = B (σ₂ v) (σ₂ w) - B v w := p2 w v
    simp only [LinearEquiv.trans_apply]
    linear_combination h₁ + h₂


--instance : HMul (B.Sp)  (B.Sp) (B.Sp) := SubGL.instHMul

--#synth HMul  B.Sp B.Sp B.Sp

variable (a b : B.Sp)

instance instFact_isAltOne : Fact (B.isAlt 1) where
  out := fun _ _ => by simp only [LinearEquiv.coe_one, id_eq, sub_self]


@[simp]
lemma map_one (v : V): (1 : Sp B) v = v := by rfl

#synth MulOneClass (Sp B)

instance instFact_isAutInv : Fact (∀ {σ}, B.isAlt σ → B.isAlt σ.symm) where
  out := by
    intro σ p w v
    have fun_inv_fun  : ∀ v, σ (σ.symm v)  = v
    := by simp only [LinearEquiv.apply_symm_apply, implies_true]
    have h :=  p (σ.symm w) (σ.symm v)
    repeat rw [fun_inv_fun] at h
    linear_combination -h

#synth Group B.Sp

end LinearMap.BilinForm.Sp
end Symplectic_Group

section PS_Group

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]
variable (B : LinearMap.BilinForm K V) --[hnd : NonDegenerate (alternatingform B)]


abbrev LinearMap.BilinForm.associated (σ :V≃ₗ[K] V ) (f : QuadraticForm K V) := ∀ w v, QuadraticMap.polar f w v = B (σ w) (σ v) - B w v

abbrev LinearMap.BilinForm.Ps :=
  {σ : (V≃ₗ[K] V) × (QuadraticForm K V) // B.associated σ.1 σ.2}

abbrev LinearMap.BilinForm.Ps.σ (a : B.Ps):= a.1.1
abbrev LinearMap.BilinForm.Ps.f (a : B.Ps):= a.1.2

lemma comp_associatedB  (a b : B.Ps) : ∀ w v, QuadraticMap.polar (b.f + ((a.f).comp (b.σ).toLinearMap)) w v = B ((a.σ * b.σ) w) ((a.σ * b.σ) v) - B w v := by
  sorry
  /-
  intro w v
  simp [form, Sp.mul_def]
  have h1 : b.f (w + v) - b.f w - b.f v = B (b.σ.σ w) (b.σ.σ v) - B w v := b.associatedB w v
  have h2 : a.f (b.σ.σ w +  b.σ.σ v) - a.f (b.σ.σ w) - a.f (b.σ.σ v) = B (a.σ.σ (b.σ.σ w)) (a.σ.σ (b.σ.σ v)) - B (b.σ.σ w) (b.σ.σ v) := by
    exact a.associatedB (b.σ.σ w) (b.σ.σ v)
  linear_combination h1 + h2
  -/

instance : HMul (B.Ps)  (B.Ps) (B.Ps) where
  hMul := fun a b =>  ⟨ ((a.σ) * (b.σ), b.f + ((a.f).comp  (b.σ).toLinearMap)), comp_associatedB B a b⟩

end PS_Group

lemma  mul_def (a b : Ps B) : a * b = ⟨a.1 * b.1, b.f + a.f ∘ b.1, add_quadraticform (b.2) (a.2 ∘ b.1.1) (b.3) (comp_quadraricform B a.2 b.1 a.3), comp_associatedB B a b⟩:= rfl

instance instSemigroup : Semigroup (Ps B) where
  mul := HMul.hMul
  mul_assoc := by
    intro a b c
    simp [mul_def]
    constructor
    · rfl
    · ext x
      simp [add_assoc]

variable {B} in
lemma neg_comp_quadratic (σ : Sp B) {f : V → K} (h : Quadraticform f) : Quadraticform ((-f) ∘ (σ)) := by
  constructor
  · constructor
    · intro r w v
      simp [form]
      have h := h.bilinear.llinear (σ r) (σ w) (σ v)
      simp [form,<-Sp.linear] at h
      linear_combination -h
    · intro r w v
      simp [form]
      have h := h.bilinear.rlinear (σ r) (σ w) (σ v)
      simp [form,<-Sp.linear] at h
      linear_combination -h
    · intro r w v
      simp [form, Sp.linear, Sp.slinear]
      have h := h.bilinear.lslinear r (σ w) (σ v)
      simp_all [form]
      linear_combination -h
    · intro r w v
      simp [form, Sp.linear, Sp.slinear]
      have h := h.bilinear.rslinear r (σ w) (σ v)
      simp_all [form]
      linear_combination -h
  · intro t v
    simp [h.sq_smul,Sp.slinear]



variable {B} in
lemma inv_associatedB (σ : Sp B) {f : V → K} (hB : ∀ w v, form f  w v = B (σ w) (σ v) - B w v ): ∀ w v, form ((-f) ∘ (σ⁻¹:Sp B)) w v = B (σ⁻¹ w) (σ⁻¹ v) - B w v := by
  intro w v
  simp [form,linear]
  have h := hB (σ⁻¹ w) (σ⁻¹ v)
  rw [form] at h
  simp only [<-Sp.map_mul,mul_inv_cancel, Sp.map_one] at h
  linear_combination - h

instance  instInv: Inv  (Ps B) where
   inv := fun a => ⟨a.σ⁻¹ , (- a.f) ∘ (a.σ⁻¹ : Sp B) , neg_comp_quadratic (a.σ⁻¹) a.Quaf, inv_associatedB a.σ a.associatedB⟩

--omit hnd in
lemma inv_def (a : Ps B) : a⁻¹ =
⟨a.σ⁻¹ , (- a.f) ∘ (a.σ⁻¹ : Sp B) , neg_comp_quadratic (a.σ⁻¹) a.Quaf, inv_associatedB a.σ a.associatedB⟩ := rfl


lemma one_quadraticform : Quadraticform (0 : V → K) := by
  constructor
  · constructor
    · intro r w v
      simp [form]
    · intro r w v
      simp [form]
    · intro r w v
      simp [form]
    · intro r w v
      simp [form]
  · intro t v
    simp

--omit hnd in
lemma one_associatedB : ∀ w v, form 0 w v = B ((1 : Sp B) w) ((1 : Sp B) v) - B w v := by
  intro w v
  simp [form]

instance hasOne: One (Ps B)  where
  one := ⟨(1 : Sp B), 0, one_quadraticform, one_associatedB B⟩



@[simp]
lemma One_def : (1 : Ps B) = ⟨(1 : Sp B), 0, one_quadraticform, one_associatedB B⟩ := rfl



instance instMulOneClass : MulOneClass (Ps B) where
  one_mul := by
    intro a
    rw [mul_def]
    ext v;unfold Ps.σ
    · rw [One_def,coe_map,Sp.map_mul,Sp.map_one,Sp.coe_map]
    · simp only [One_def, Pi.zero_comp, Pi.add_apply, Pi.zero_apply, add_zero]
  mul_one := by
    intro a
    rw [mul_def]
    ext v
    · rw [One_def,coe_map,Sp.map_mul,Sp.map_one,Sp.coe_map]
    · simp only [One_def, Pi.add_apply, Pi.zero_apply, comp_apply, zero_add]
      rfl




instance instMonoid : Monoid (Ps B) where
  one_mul := one_mul
  mul_one := mul_one
  npow := npowRecAuto
  npow_zero := by intros; rfl
  npow_succ := by intros; rfl

noncomputable instance instGroup : Group (Ps B) where
inv_mul_cancel := by
  intro a
  rw [mul_def,inv_def]
  ext v
  · simp only [inv_mul_cancel, One_def]
  · simp only [Pi.add_apply, comp_apply, coe_map, self_of_map_inv_self, Pi.neg_apply,
    add_neg_cancel, One_def, Pi.zero_apply]

instance instSmul : SMul (Ps B) (Heisenberg B) where
  smul := fun s h => (s.σ h.1, s.f h.1 + h.2)

lemma smul_def (s : Ps B) (h : Heisenberg B) : s • h =  (s.σ h.1, s.f h.1 + h.2) := by rfl

instance instMulAction : MulAction (Ps B) (Heisenberg B) where
  smul := SMul.smul
  one_smul := by
    intro b
    simp [smul_def]
  mul_smul := by
    intro x y b
    simp [smul_def, mul_def, ← add_assoc, add_comm]




end pseudo_symplectic

end Pseudo_Symplectic_Group
