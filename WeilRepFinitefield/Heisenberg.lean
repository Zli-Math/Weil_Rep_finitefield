import Mathlib

import WeilRepFinitefield.Compute

section HeisenbergGroup


variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V][Module K V]



variable (B : LinearMap.BilinForm K V)

abbrev Heisenberg (B : LinearMap.BilinForm K V)
 := V × K

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

end LinearMap.BilinForm


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
    ext
    · simp only [add_assoc]
    · simp_rw [B.rlinear,B.llinear]
      abel



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




end Heisenberg

end HeisenbergGroup



section Eg

local notation "V2" => (Fin 1 → (ZMod 2))
local notation "KK" => (ZMod 2)

abbrev BB : LinearMap.BilinForm KK V2 := !![1].toBilin'

abbrev a : Heisenberg (BB) := ⟨1,0⟩

#eval a

example : a * a = ⟨0,1⟩ := by decide


end Eg
