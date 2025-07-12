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


abbrev Polarization.cocycle_aux [DecidableEq R] [DecidableEq V] [Fintype Y] : R := ((ω s1).toMatrix' * (ω s2).toMatrix' * (ω (s1 * s2)).toMatrix'⁻¹).trace


abbrev Polarization.cocycle [DecidableEq R] [DecidableEq V] [Fintype Y] : R := (P.cocycle_aux χ s1 s2) / (Fintype.card Y)


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
  χ₀ (s1.f w1 + ⟪s1.ws, w1⟫ + B (u1) (w1 + s1.ws) + s2.f w2 + ⟪s2.ws, w2⟫) * χ₀ (B (u2) (w2 + s2.ws) + B (u1 + s1.ws) (w2 + s2.ws)))

instance : FinEnum s1.I := sorry




abbrev sqrtrank {R : Type*} [Semiring R] (b0 : ℕ) (b1 : R) (α : Type*) [Fintype α] := b1 ^ (Nat.log b0 (Fintype.card α))

variable [hsqrt2 : HRadical 2 (2 :R)]

abbrev Ps.cgamma  := sqrtrank 2 hsqrt2.r s1.I * sqrtrank 2 hsqrt2.r s2.I / sqrtrank 2 hsqrt2.r s2.I

abbrev Ps.ncocycle :=  s1.cgamma s2 * s1.cocycle' χ₀ s2



section doublecover
@[ext]
structure DPs where
  s : B.Ps
  z : ZMod 2

variable [DecidableEq R]

namespace DPs
abbrev mul : B.DPs →B.DPs → B.DPs :=
  fun a b =>
  let c := a.s.ncocycle χ₀ (b.s)
  { s := a.s * b.s, z := a.z + b.z +
    if c = -1  then 1 else 0 }

end DPs

end doublecover

end LinearMap.BilinForm
