import Mathlib
--import WeilRepFinitefield.HeisenbergRepresentation
import WeilRepFinitefield.HeisenbergRepresentation
import WeilRepFinitefield.PseudoSymplecticGroup

open Module
open BigOperators
open Schrodinger_Model
open Finset Fintype
open Classical

variable {K : Type } [Field K]  {V : Type }  [AddCommGroup V] [Module K V] {R : Type*} [Field R]
variable (B : LinearMap.BilinForm K V)

local notation3 "⟪" a:40 "," b:40 "⟫" => (B.toAlt) a b

variable {X Y : Submodule K V} (χ₀ : AddChar K R) (P : B.Polarization X Y)
variable (h : B.Heisenberg)

variable (χ : (B.toSubgroup X) →* Rˣ) [isextendchara : extendcharacter B χ₀ χ]

variable (σ : B.Sp)
variable (s : B.Ps)
variable (v w : V)

namespace LinearMap.BilinForm

@[simp]
lemma toAlt.llinear_form : ∀ w v r, ⟪w + r, v⟫ = ⟪w, v⟫ + ⟪r, v⟫ := by
  intro w v r
  simp only [LinearMap.sub_apply, map_add, LinearMap.add_apply, LinearMap.BilinForm.flip_apply]

@[simp]
lemma toAlt.rlinear_form : ∀ w v r, ⟪w, v + r⟫ = ⟪w, v⟫ + ⟪w, r⟫ := by
  intro w v r
  simp only [LinearMap.sub_apply, map_add, flip_apply, LinearMap.add_apply]


local notation "ρ" => (P.rhoY χ)

#check ρ

variable [Fintype K] [Fintype V] [DecidableEq K][DecidableEq V]

#synth HSMul (B.Ps) (B.Heisenberg) (B.Heisenberg)

variable {B} in
def Polarization.omega_aux (s : B.Ps) (w : V): End R (P.Ymodel R) :=
  ∑ (v : V) , ρ  ((s • (B.toH v))⁻¹ * (B.toH w) * (B.toH v))

#print LinearMap.BilinForm.Polarization.omega_aux

variable {B}
abbrev Ps.assoc (v : V) :=
 ∀ w, s.σ w = w → (s.f w) =  ⟪v,w⟫


abbrev Ps.Ws := {v | s.assoc v}


--instance  [Fintype V] [DecidableEq V] [DecidableEq K]: Decidable (∀ w, s.σ w = w → (s.f w) =  ⟪v,w⟫) := by infer_instance





lemma Ps.Ws_nonempty : Nonempty (s.Ws) := by sorry


variable [FiniteDimensional K V] [Nonempty V] [char2: CharP K 2]

/-
noncomputable section test

variable (α : Type*) [Fintype α]

#synth FinEnum α

end test
-/

variable [FinEnum V]



def Ps.ws : V := @FinEnum.some s.Ws _ s.Ws_nonempty

abbrev Polarization.omega : End R (P.Ymodel R) := P.omega_aux χ s  (s.ws)

local notation "ω" => (P.omega χ)

open LinearMap.BilinForm
open Heisenberg
open Polarization

#check hmul_def

lemma weq_lemma (H : wₛ ∈ s.Ws):
∀ w : V, (s • h) * (s • B.toH w)⁻¹ * (B.toH wₛ) * (B.toH  w)  =  (s • B.toH (w - h.1))⁻¹ * (B.toH wₛ) * (B.toH (w - h.1)) * h := by
  intro w
  simp only [LinearMap.BilinForm.Ps.smul_def, LinearMap.BilinForm.toH_def, add_zero, map_sub,LinearMap.BilinForm.Heisenberg.mul_def]
  have h1: - s.σ (-h.1) = s.σ (h.1) := by simp only [map_neg, neg_neg]
  simp_rw [inv_def B]
  rw [Prod.ext_iff]
  constructor
  · simp [add_assoc]
    rw [← AddCommSemigroup.toAddSemigroup.add_assoc]
    simp only [sub_eq_add_neg]
  · sorry


--Prop 3.2 (1)
lemma omega_intertwine : (ρ (s • h)) ∘ₗ  (ω s) = (ω s) ∘ₗ (ρ h) := by
  unfold omega; unfold omega_aux
  rw [<-LinearMap.mul_eq_comp,Finset.mul_sum]
  rw [<-LinearMap.mul_eq_comp,Finset.sum_mul]
  simp_rw [rhoY.map_mul]
  set v := h.1
  sorry

--#synth Inv (Matrix  (Fin (2)) (Fin (2)) (ZMod 2))
--define gamma function
variable (s1 s2 : Ps B)


abbrev Polarization.cocycle [DecidableEq R] [DecidableEq V] [Fintype Y] : R := ((ω s1).toMatrix' * (ω s2).toMatrix' * (ω (s1 * s2)).toMatrix'⁻¹).trace


abbrev Ps.I := LinearMap.range (LinearMap.id - s.σ.toLinearMap)


abbrev Ps.I' := Set.range (fun v => v -  s.σ v)


abbrev Ps.I₀ := { ((u1, u2) : (s1.I ) × (s2.I)) |  u1.1 + u2.1  = (s1 * s2).ws - s1.ws - s2.ws}

--instance FintypeI : Fintype (s1.I₀ s₂) := Subtype.fintype _

variable {s} in
abbrev Ps.I.fiber (u : s.I) := {w | w - s.σ w = u}

instance (u : s.I) : Nonempty { w | w - s.σ w =u} := by
  obtain ⟨u,w,hw⟩ := u
  use w
  simp only [LinearMap.sub_apply, LinearMap.id_coe, id_eq, LinearEquiv.coe_coe] at hw
  exact hw

abbrev Ps.fiberw (u : s.I) := FinEnum.some { w | w - s.σ w =u}


abbrev Ps.cocycle' :=  (∑ ((u1, u2) ∈ (s1.I₀ s2)),
  let w1 := s1.fiberw u1
  let w2 := s2.fiberw u2
  χ₀ (s1.f w1 + ⟪s1.ws, w1⟫ + B (u1) (w1 + s1.ws) + s2.f u2 + ⟪s2.ws, w2⟫) * χ₀ (B (u2) (w2 + s2.ws) + B (u1 + s1.ws) (w2 + s2.ws)))


end LinearMap.BilinForm




abbrev Ker : AddSubgroup V where
  carrier := {w : V| s.σ w = w }
  add_mem' := by
    intro a b ha hb
    simp_all [Sp.linear]
  zero_mem' := by
    simp
    have := Sp.slinear (s.σ) (0 : K) (w : V)
    simp at this
    exact this
  neg_mem' := by
    intro x hx
    simp_all
    have : -x = (-1 : K) • x := by rw [neg_one_smul]
    rw [this, Sp.slinear]
    simp [hx]
instance FintypeK : Fintype (Ker s w) := Subtype.fintype _


def id_σ : AddMonoidHom V V where
  toFun := id - s.σ.1.toFun
  map_zero' := by simp
  map_add' := by
    intro x y
    simp
    rw [← sub_sub, sub_eq_add_neg (x + y) _, add_assoc, add_comm y _, ← add_assoc, add_sub, ← sub_eq_add_neg]

omit [Fintype K] [Fintype V] [FiniteDimensional K V] [Nonempty V] char2 hnd [IsBilinear B] in
lemma cong1 : Ker s w = (id_σ s).ker := by
  ext x
  constructor
  · simp [id_σ]
    intro h
    rw [Sp.coe_map, h]
    simp
  · simp [id_σ]
    intro h
    rw [Sp.coe_map] at h
    symm
    exact eq_of_sub_eq_zero h

omit [Fintype K] [Fintype V] [FiniteDimensional K V] [Nonempty V] char2 hnd [IsBilinear B] in
lemma cong2 : I s w = (id_σ s).range := by
  ext x
  constructor
  · simp [id_σ]
    intro v hv
    use v
    rw [Sp.coe_map, hv]
  · simp [id_σ]
    intro v hv
    use v
    rw [Sp.coe_map] at hv
    exact hv

def quotientkers : ∀ (s : Ps B), V ⧸ (Ker s w) ≃+ (I s) := by
  intro s
  rw [cong1, cong2]
  exact QuotientAddGroup.quotientKerEquivRange (id_σ s)

--instance : HVAdd V (Ker s w) (V ⧸ Ker s w) := by sorry



local notation "Ks" => Fintype.card (Ker s w)



lemma weq' : ∀ w : V, (s • w : Heisenberg B)⁻¹ * (((ws χ₀ s), 0) : Heisenberg B) * ((w , 0) : Heisenberg B) = (w - s.σ w + ws χ₀ s, s.f w + ⟪ws χ₀ s, w⟫ + B (w - s.σ w) (ws χ₀ s + w))  := by
    intro w
    simp [Heisenberg.inv_def, Heisenberg.mul_def, pseudo_symplectic.smul_def]
    constructor
    · simp [add_comm, ←add_assoc, sub_eq_add_neg]
    · simp [alternatingform, IsBilinear.llinear]
      have h1 : B (s.σ w) (s.σ w) + B (- s.σ w) w =  B (w - s.σ w) w:= by
        simp [sub_eq_add_neg, IsBilinear.llinear]
        have eq1 : s.f w + s.f w = 0:= by
          simp [← two_mul]
          left
          apply CharP.ofNat_eq_zero
        have eq2 : B (s.σ w) (s.σ w) - B w w = s.f (w + w) := by
          rw [← s.associatedB w w]
          simp [form, sub_sub, eq1]
        suffices h : s.f (w + w) = 0
        rw [h] at eq2
        rw [← add_left_inj (B w w)] at eq2
        simp at eq2
        exact eq2
        have : w + w = 0 := by rw [← two_smul K w, CharTwo.two_eq_zero, zero_smul]
        rw [this]
        have : s.f ((0 : K) • 0) = 0 ^ 2 * s.f 0 := by apply s.Quaf.sq_smul 0 0
        simp at this
        exact this
      have h2 : - s.f w = s.f w := CharTwo.neg_eq (s.f w)
      simp [add_assoc, h2]
      rw [← add_assoc, ← add_assoc, add_comm, sub_add]
      simp [sub_eq_add_neg]
      rw [add_comm (B (s.σ w) (s.σ w)) _, add_assoc, h1]
      simp [IsBilinear.llinear, IsBilinear.rlinear]
      ring_nf
      simp [add_assoc, sub_eq_add_neg, IsBilinear.llinear]

lemma weq'' : let f := fun x:V => (rhoY hp χ) ((s • x : Heisenberg B)⁻¹ * (((ws χ₀ s), 0) : Heisenberg B) * (x , 0)); ∀ v ∈ Ker s w, f (w + v) = f w:= by
  intro f v hv

  have : ∀ x, f x =  (χ₀ (s.f x + ⟪(ws χ₀ s),x⟫ + B (x - s.σ x) ((ws χ₀ s) + x))) • ρ (x - s.σ x + (ws χ₀ s)) := by
    intro x
    simp [f, weq']
    apply rhoY.eq'
  simp [this]

  have : s.f (w + v) = s.f w + s.f v + B (s.σ w) (s.σ v) - B w v := by
    rw [← add_sub, ← Ps.associatedB s w v, form]
    ring
  simp [this]
  simp [Ker] at hv

  have : w + v - s.σ (w + v) = w - s.σ w := by
    simp [Sp.linear, sub_eq_add_neg, add_assoc]
    simp [← add_assoc]
    rw [← sub_eq_add_neg, sub_eq_zero]
    symm
    exact hv
  simp [this]
  rw [← add_assoc (ws χ₀ s: V) w v ]
  simp [IsBilinear.rlinear ((ws χ₀ s) + w) (w - s.σ w) v]

  have : B (s.σ w) (s.σ v) - B w v + B (w - s.σ w) v = 0 := by
    simp [sub_eq_add_neg, IsBilinear.llinear, hv]
    ring_nf
    simp [← IsBilinear.llinear]
  rw [add_comm (B (w - s.σ w) (↑(ws χ₀ s) + w)) _, add_assoc, ← add_assoc (⟪↑(ws χ₀ s),w + v⟫) _ _, add_comm (⟪↑(ws χ₀ s),w + v⟫) _, ← add_assoc, ← add_assoc, ← add_sub, add_assoc (s.f w + s.f v) _ _]
  simp [this, rlinear_form]

  have : χ₀ (s.f w + s.f v + (⟪↑(ws χ₀ s),w⟫ + ⟪↑(ws χ₀ s),v⟫) + B (w - s.σ w) (↑(ws χ₀ s) + w)) = χ₀ (s.f v +  ⟪↑(ws χ₀ s),v⟫) * χ₀ (s.f w + ⟪↑(ws χ₀ s),w⟫ + B (w - s.σ w) (↑(ws χ₀ s) + w)) := by
    calc
      _ = χ₀ (s.f v +  ⟪↑(ws χ₀ s),v⟫ + s.f w + ⟪↑(ws χ₀ s),w⟫ + B (w - s.σ w) (↑(ws χ₀ s) + w)) := by
        rw [add_comm (s.f w), add_assoc (s.f v), ← add_assoc (s.f w), add_comm _ (⟪↑(ws χ₀ s),v⟫), ← add_assoc, ← add_assoc]
      _ = χ₀ (s.f v + ⟪↑(ws χ₀ s),v⟫) * χ₀ (s.f w + ⟪↑(ws χ₀ s),w⟫ + B (w - s.σ w) (↑(ws χ₀ s) + w)) := by
        rw [add_assoc, add_assoc, ← add_assoc (s.f w)]
        apply AddChar.map_add_eq_mul χ₀ (s.f v + ⟪↑(ws χ₀ s),v⟫) (s.f w + ⟪↑(ws χ₀ s),w⟫ + B (w - s.σ w) (↑(ws χ₀ s) + w))
  simp [this]
  rw [← smul_smul, ← rhoY.eq']

  have : χ₀ (s.f v + ⟪↑(ws χ₀ s),v⟫) = 1 := by
    rw [AddChar.map_add_eq_mul χ₀ (s.f v) _]
    have := (ws χ₀ s).2
    simp only [Ws] at this
    rw [Set.mem_setOf] at this
    have H := this v hv
    rw [← H, ← AddChar.map_add_eq_mul]
    have : s.f v + s.f v = 0:= by
      simp [← two_mul]
      left
      apply CharP.ofNat_eq_zero
    rw [this]
    exact AddChar.map_zero_eq_one χ₀

  simp [this]

lemma coset_eq : let f := fun x:V => (rhoY hp χ) ((s • x : Heisenberg B)⁻¹ * (((ws χ₀ s), 0) : Heisenberg B) * (x , 0)); (Ks : ℂ)⁻¹ • ( ∑ v : V, f (v)) =  (∑ u : I s w, f u.2.choose) := by
  intro f
  have : ∑ v : V, f v = (Ks : ℂ) • (∑ x : V ⧸ Ker s w, f x.out ):= by
    --have : V = ⋃(x : V ⧸ Ker s w), Quotient.out x +ᵥ (Ker s w) := by sorry
    sorry
  rw [this]
  let g := fun u : I s w => f u.2.choose
  have hequiv : Function.Bijective (quotientkers w s).1 := by apply Equiv.bijective (quotientkers w s).1
  have hg : ∑ x : V ⧸ (Ker s w), f x.out = ∑  x : V ⧸ (Ker s w), g ((quotientkers w s).1 x) := by
    simp
    sorry
  rw [hg, smul_smul, inv_mul_cancel_of_invertible, one_smul]
  apply Function.Bijective.sum_comp hequiv g


--Prop 3.2 (2)
lemma omega_eq : ∀ s, (Fintype.card (Ker s w) : ℂ)⁻¹ • ω s =  (∑ (u : (I s w)), χ₀ ((s.f u.2.choose) + ⟪ws χ₀ s, u.2.choose⟫ + B u (ws χ₀ s + u.2.choose )) • ρ (u + ws χ₀ s)) := by
  unfold omega; unfold omega_aux
  intro s
  rw [coset_eq]
  simp only [weq']
  set f := fun u : I s w => (rhoY hp χ) (u.2.choose - s.σ u.2.choose + (ws χ₀ s), s.f u.2.choose + ⟪(ws χ₀ s), u.2.choose⟫ + B (u.2.choose - s.σ u.2.choose) ((ws χ₀ s) + u.2.choose))
  have : ∀ u, f u =  (χ₀ (s.f u.2.choose + ⟪(ws χ₀ s), u.2.choose⟫ + B (u) (ws χ₀ s + u.2.choose) )) • ρ (u + (ws χ₀ s)) := by
    intro x
    simp [f]
    have : ∀ u : (I s w), u.2.choose - s.σ u.2.choose = u := by
      intro u
      have := u.2
      apply Exists.choose_spec this
    rw [this]
    apply rhoY.eq'
  simp [this]



--Proof of Corollory 3.4
lemma cocycle_omega : (γ (s₁.σ) • ((Fintype.card (Ker s₁ w) : ℂ)⁻¹ • ω s₁)) * (γ (s₂.σ) • (((Fintype.card (Ker s₂ w) : ℂ)⁻¹) • ω s₂)) =  c • (γ (s₁.σ * s₂.σ) • ((Fintype.card (Ker (s₁ * s₂) w) : ℂ)⁻¹) •  ω (s₁ * s₂)):= by
  simp only [omega_eq]
  rw [mul_smul_comm, smul_mul_assoc, Finset.sum_mul_sum]
  have : ∀ (i : I s₁ w) (j : I s₂ w), χ₀ (s₁.f (i.2.choose) + ⟪(ws χ₀ s₁), i.2.choose⟫ + B i ((ws χ₀ s₁) + i.2.choose)) • (rhoY hp χ) (i + (ws χ₀ s₁)) * χ₀ (s₂.f j.2.choose + ⟪(ws χ₀ s₂), j.2.choose⟫ + B j ((ws χ₀ s₂) + j.2.choose)) • (rhoY hp χ) (j + (ws χ₀ s₂)) =  (χ₀ (s₁.f i.2.choose + ⟪(ws χ₀ s₁), i.2.choose⟫ + B (i.2.choose - s₁.σ i.2.choose) ((ws χ₀ s₁) + i.2.choose) + s₂.f j.2.choose + ⟪ws χ₀ s₂, j.2.choose⟫) * χ₀ (B (j.2.choose - s₂.σ j.2.choose) (ws χ₀ s₂ + j.2.choose) + B ((i.2.choose - s₁.σ i.2.choose) + (ws χ₀ s₁)) ((j.2.choose - s₂.σ j.2.choose) + ws χ₀ s₂)))• (rhoY hp χ) (i + j + (ws χ₀ s₁) + (ws χ₀ s₂)) := by
    intro x y
    rw [smul_mul_smul_comm]
    have h1 : (rhoY hp χ) ( x + (ws χ₀ s₁)) * (rhoY hp χ) (y + (ws χ₀ s₂)) = χ₀ (B (x + (ws χ₀ s₁)) (y + (ws χ₀ s₂))) • (rhoY hp χ) ( x + y + (ws χ₀ s₁) + (ws χ₀ s₂)) := by
      rw [rhoY.map_mul]
      simp [Heisenberg.mul_def]
      rw [rhoY.eq' B χ₀ hp χ]
      congr 2
      simp [add_assoc]
      simp [← add_assoc]
      rw [add_comm]
    rw [h1, smul_smul]
    simp [← AddChar.map_add_eq_mul]
    congr 2
    simp [add_assoc]
    have := Exists.choose_spec x.2
    simp [this]
    have := Exists.choose_spec y.2
    simp [this]
  simp_rw [this]






  sorry


--Corollory 3.6
lemma range_of_cocycle : c ∈ ({1, -1} : Set ℂ ) ↔ ∀ w1 w2, B (s₁.σ w1) (s₁.σ w2) = B w1 w2 ∧ B (s₂.σ w1) (s₂.σ w2) = B w1 w2 ∧ θ s₁.σ + θ s₂.σ - θ (s₁.σ * s₂.σ) ≡ 0 [PMOD π] := by
  constructor
  · intro h w1 w2
    sorry
  · sorry





class value_of_cocycle where
value : c  ∈ ({1, -1} : Set ℂ )

variable [Gamma_condition: value_of_cocycle χ₀ w s₁ s₂ w₁ w₂ w₁₂ γ]


--Define Weil representation of Ps B
--Definition 3.8
structure cover_of_Ps where
s : Ps B
integer : ℤ
omega : End ℂ (Ymodel hp)
relation :  omega = (-1 : ℂ) ^ integer • ω s


--Corollory 3.10
structure Weil_rep where
rep : cover_of_Ps χ₀ hp χ →  End ℂ (Ymodel hp)
equation : ∀ (s : cover_of_Ps χ₀ hp χ), rep s = s.3


structure Character_of_Weil_rep (s : cover_of_Ps χ₀ hp χ) where
existw : ∃ w, s.s.σ w - w = ws χ₀ s.s
char := fun (s : cover_of_Ps χ₀ hp χ) => (-1 : ℂ) ^ (s.integer) * γ (s.s.σ) * Fintype.card (Y) * χ₀ (s.s.f existw.choose - B (s.s.σ existw.choose) (ws χ₀ s.s))



end
