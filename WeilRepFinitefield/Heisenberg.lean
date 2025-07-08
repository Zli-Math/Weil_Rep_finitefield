import Mathlib

import WeilRepFinitefield.Compute

section HeisenbergGroup


variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V][Module K V]



variable (B : LinearMap.BilinForm K V)

abbrev Heisenberg (B : LinearMap.BilinForm K V)
 := V × K

abbrev Heisenberg.mk (w : V) (k : K) : Heisenberg B := ⟨w,k⟩


@[ext]
lemma Heisenberg.ext (a b : Heisenberg B) (h1 : a.1 = b.1) (h2 : a.2 = b.2) : a = b := by
  unfold Heisenberg at *
  ext <;> assumption


instance Heisenberg.coeV : Coe V (Heisenberg B) where
  coe := fun v => ⟨v,0⟩


class IsBilinear (B : V →  V → K) where
  llinear : ∀ r w v , B (r + w) v =  B r v + B w v
  rlinear : ∀ r w v , B w (r + v) = B w r + B w v
  lslinear: ∀ (r : K) (w v : V) , B (r • w) v = r * B w v
  rslinear: ∀ (r : K) (w v : V) , B w (r • v) = r * B w v

namespace LinearMap.BilinForm
lemma  llinear : ∀ r w v , B (r + w) v =  B r v + B w v := by simp
lemma  rlinear : ∀ r w v , B w (r + v) = B w r + B w v := by simp
lemma  lslinear: ∀ (r : K) (w v : V) , B (r • w) v = r * B w v := by simp
lemma rslinear: ∀ (r : K) (w v : V) , B w (r • v) = r * B w v := by simp


abbrev toAlt := B - B.flip

lemma toAlt_isAlt : B.toAlt.IsAlt := by intro; simp



end LinearMap.BilinForm

section NonDegenerate

class NonDegenerate (B : LinearMap.BilinForm K V) where
  nondeg: B.Nondegenerate


end NonDegenerate



namespace Heisenberg


--variable [bilinearB : IsBilinear B]
lemma B_neg_neg (w v :V) : B w v = B (-w) (-v) := by
  rw [← neg_one_smul K w, ← neg_one_smul K v]
  simp only [B.lslinear, B.rslinear]
  simp

instance : HMul (Heisenberg B) (Heisenberg B) (Heisenberg B) where
  hMul := fun a b => ⟨ a.1 + b.1 , a.2 + b.2 + B  a.1  b.1 ⟩

lemma mul_def (a b : Heisenberg B) : a * b = ⟨ a.1 + b.1 , a.2+ b.2 + B a.1 b.1 ⟩ := rfl


instance instSemigroup : Semigroup (Heisenberg B) where
  mul := (· * · )
  mul_assoc := by
    intro a b c
    repeat rw [mul_def]
    simp
    constructor
    · simp only [add_assoc]
    · abel



instance instInv: Inv  ( Heisenberg B) where
   inv := fun a => ⟨ -a.1 , -a.2 + B  a.1  a.1⟩

lemma inv_def (a : Heisenberg B) : a⁻¹ =  ⟨ -a.1 , -a.2 + B  a.1  a.1⟩ := rfl

@[simp]
lemma Blzero (b:  V) : B  0  b  = 0 := by
  have h : B 0 b = B 0 b := by rfl
  nth_rewrite 1 [←zero_add 0] at h
  rw [B.llinear] at h
  simp at *

@[simp]
lemma Brzero (b:  V) : B  b 0 = 0 := by
  have h : B b 0 = B b 0 := by rfl
  nth_rewrite 1 [←zero_add 0] at h
  rw [B.rlinear] at h
  simp at *

instance hasOne: One (Heisenberg B)  where
  one := ⟨0,0⟩

@[simp]
lemma One_def1 : (1 :Heisenberg B).1 =0 := rfl

@[simp]
lemma One_def2 : (1 :Heisenberg B).2 =0 := rfl


instance instMulOneClass : MulOneClass (Heisenberg B) where
  one_mul := by simp [mul_def]
  mul_one := by simp [mul_def]



instance instMonoid : Monoid (Heisenberg B) where
  one_mul := by simp
  mul_one := by simp
  npow := npowRecAuto
  npow_zero := by intros; rfl
  npow_succ := by intros; rfl

instance instGroup : Group (Heisenberg B) where
  one_mul := one_mul
  mul_one := mul_one
  inv_mul_cancel := by
    intro a
    rw [mul_def,inv_def]
    calc
      _ = ⟨0, B a.1 a.1 + B (-a.1) a.1⟩  := by simp
      _ = ⟨0, B 0 a.1⟩  := by simp [<-IsBilinear.llinear]
      _ = ⟨0,0⟩  := by simp [Blzero]
      _ = _ := by rfl


abbrev C : Subgroup (Heisenberg B) := Subgroup.center _

abbrev SubK : Subgroup (Heisenberg B) where
  carrier := { a | a.1 = 0 }
  mul_mem' := by
    intro a b ha hb
    simp_all
    rw [mul_def]
    simp [ha , hb]
  one_mem' := by
    simp
  inv_mem' := by
    intro x h
    simp_all
    simp [inv_def , h]


--Proposition 1.4
theorem centralextension : (SubK B).carrier ⊆ (C B).carrier := by
  intro x h
  simp [SubK] at h
  rw [Subgroup.mem_carrier]
  rw [Subgroup.mem_center_iff]
  intro y
  repeat rw [mul_def]
  simp [add_comm , h]
--Subgroup.subgroupOf

theorem center_is_K_of_nondegenerateB [hnd: NonDegenerate B.toAlt ] : (SubK B) = (C B) := by
  have nondege  := hnd.1
  ext x
  constructor
  apply centralextension
  intro h
  simp [SubK , C] at h ⊢
  rw [Subgroup.mem_center_iff] at h
  simp_rw [mul_def] at h
  simp [add_comm] at h
  simp [LinearMap.BilinForm.toAlt] at nondege
  specialize nondege x.1
  exact nondege (by convert h using 1; simp [sub_eq_zero] ; tauto
  )


variable {B w x} in
lemma add_x_dec : (w + x, t)= (Heisenberg.instHMul B |>.hMul) (⟨w , t - B w x⟩ : Heisenberg B)  (⟨x, 0⟩ : Heisenberg B)  := by simp [Heisenberg.mul_def]

end Heisenberg


section Polarization
variable (X Y : Submodule K V)


abbrev LinearMap.BilinForm.IsIsotropic (B : LinearMap.BilinForm K V) (X : Submodule K V):=
  ∀ x y : X, B x y = 0


class Polarization  where
  iota : (X × Y)  ≃ₗ[K] V
  embed : ∀ x : X, ∀ y: Y, iota ⟨x,y⟩ = x.1+y.1
  Xisotropic : B.toAlt.IsIsotropic X
  Yisotropic : B.toAlt.IsIsotropic Y

variable {X Y} (P : Polarization B X Y)

namespace Polarization
variable {B}

abbrev iota' := P.iota.symm

@[simp]
lemma sum_coor (v : V) : (P.iota' v).1.1 + (P.iota' v).2.1 = v := by
  rw [<-P.embed]
  have : ⟨(P.iota' v).1, (P.iota' v).2⟩ = P.iota' v := rfl
  simp only [this, LinearEquiv.apply_symm_apply]


def X_coor (w : Heisenberg B) : X := (P.iota' w.1) |>.1
def Y_coor (w : Heisenberg B) : Y := (P.iota' w.1) |>.2



lemma element_XY : ∀ w : Heisenberg B, w = ((P.X_coor w).1 + (P.Y_coor w).1, w.2):= by
  intro w
  ext
  · simp only [Polarization.X_coor, Polarization.Y_coor, Polarization.sum_coor]
  · rfl

lemma element_of_V_XY : ∀ w : V, w = (P.X_coor w).1 + (P.Y_coor  w).1:= by
  intro
  simp [Polarization.X_coor, Polarization.Y_coor, P.sum_coor]

lemma coor_of_eq : ∀ w , ∀ x : X, ∀ y : Y,  (w.1  = x.1 + y.1) → (P.X_coor w) = x ∧ P.Y_coor w = y := by
  intro w x y hw
  have H:= P.element_XY w
  rw [H] at hw
  simp only [<-P.embed ] at hw
  apply_fun P.iota.symm at hw
  simp only [LinearEquiv.symm_apply_apply, Prod.mk.injEq] at hw
  exact hw




lemma coor_linear : ∀ w v, w * v =  ((P.X_coor w).1 + (P.Y_coor w).1 + ((P.X_coor v).1 + (P.Y_coor v).1), w.2 + v.2 + B w.1 v.1 ) := by
  intro w v
  simp [Heisenberg.mul_def]
  have hw := P.element_XY w
  have hv := P.element_XY v
  nth_rw 1 [hw, hv]


lemma XY_coor_linear : ∀ w v, (P.X_coor (w * v)).1 = (P.X_coor w).1 + (P.X_coor  v).1 ∧ (P.Y_coor  (w * v)).1 = (P.Y_coor w).1 + (P.Y_coor v).1 := by
  intro w v
  have hwv := P.coor_linear w v
  have hwv1 : (w * v).1 = ((P.X_coor w).1 + ((P.X_coor v).1) + ((P.Y_coor w).1  + (P.Y_coor v).1)) := by
    simp [hwv]
    rw [add_assoc, ← add_assoc (P.Y_coor w).1, add_comm  (P.Y_coor w).1, add_assoc (P.X_coor v).1, ← add_assoc]
  simp only [<-Submodule.coe_add,Subtype.coe_inj]
  apply coor_of_eq
  simp only [hwv1, Submodule.coe_add]





def LinearMap.BilinearForm.toSubgroup (X : Submodule K V) : Subgroup (Heisenberg B)  where
  carrier := by
    rw [Heisenberg]
    exact Set.prod X.carrier  Set.univ
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

end Polarization

end Polarization

end HeisenbergGroup



section Eg

local notation "V2" => (Fin 1 → (ZMod 2))
local notation "KK" => (ZMod 2)

abbrev BB : LinearMap.BilinForm KK V2 := !![1].toBilin'

abbrev a : Heisenberg (BB) := ⟨1,0⟩

#eval a

example : a * a = ⟨0,1⟩ := by decide


end Eg
