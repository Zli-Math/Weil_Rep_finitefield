import Mathlib

section

universe u

variable {α β γ : Type*} {R :Type u} [CommSemiring R]


instance : ∀ (n : ℕ) [NeZero n],  FinEnum (ZMod n)
  | 0, h => (h.ne _ rfl).elim
  | n + 1, _ => @FinEnum.fin (n+1)

instance  Matrix.instFinEnum [FinEnum α] [FinEnum β] [FinEnum γ] :
  FinEnum $ Matrix α β γ := by
  unfold Matrix
  infer_instance

instance  [FinEnum R] [CommSemiring R]  [FinEnum α] [FinEnum β] [DecidableEq α]
 :
  FinEnum $ (α → R) →ₗ[R] (β → R):=  @FinEnum.ofEquiv  (Matrix β α R) ((α → R) →ₗ[R] (β → R)) (Matrix.instFinEnum) (LinearMap.toMatrix'.toEquiv)

instance [Repr R]  : Repr ((Fin n → R) →ₗ[R] (Fin m → R)) where
  reprPrec := fun v _ => "(" ++ repr v.toMatrix'++").toLin'"


instance  [FinEnum R]  [FinEnum α] [DecidableEq α]
 :
  FinEnum $ LinearMap.BilinForm R (α → R) :=  @FinEnum.ofEquiv  (Matrix α α R) _ (Matrix.instFinEnum) (LinearMap.BilinForm.toMatrix'.toEquiv)


instance [Repr R]  : Repr (LinearMap.BilinForm R (Fin n → R)) where
  reprPrec := fun v _ => "(" ++ repr v.toMatrix'++").toBilin'"

section Inv


end Inv


variable [Fintype n] [DecidableEq n] [CommRing α] [Inv α]
instance (priority := 1000) Matrix.inv_of_inv : Inv (Matrix n n α):=
  ⟨fun A => A.det⁻¹ • A.adjugate⟩


--#synth Inv (MM 1)

--#eval B⁻¹


variable [Field K] [FinEnum K]  [FinEnum α] [DecidableEq α]

--#synth FinEnum $ { g : Matrix α α K // g.det ≠ 0}

def LinearEquiv.toGL' : ((α → K) ≃ₗ[K] (α → K)) ≃  { g : Matrix α α K // g.det ≠ 0} where
  toFun := fun e => by
    refine ⟨e.toMatrix',?_⟩
    have H:= LinearEquiv.isUnit_det' e
    simp only [LinearMap.det_toMatrix']
    exact IsUnit.ne_zero H
  invFun := fun g => by
    apply g.1.toLinearEquiv'
    have : Invertible g.1.det := invertibleOfNonzero g.2
    apply Matrix.invertibleOfDetInvertible
  left_inv := by
    intro g
    simp only [ne_eq, id_eq, eq_mpr_eq_cast, ← toLinearMap_inj, Matrix.toLinearEquiv'_apply,
      Matrix.toLin'_toMatrix']
  right_inv := by
    intro g
    simp only [ne_eq, Matrix.toLinearEquiv'_apply, LinearMap.toMatrix'_toLin', Subtype.coe_eta]

instance :  FinEnum $ (α → K) ≃ₗ[K] (α → K) :=  FinEnum.ofEquiv  ({ g : Matrix α α K // g.det ≠ 0})  (LinearEquiv.toGL')


unsafe instance {n : ℕ} [Repr K]  : Repr ((Fin n → K) ≃ₗ[K] (Fin n → K))  where
  reprPrec := fun v _ => "LinearEquiv.toGL'.symm ⟨" ++ repr v.toGL' ++",by decide⟩"

section test

local notation "F" => (ZMod 2)

abbrev MM n := Matrix (Fin (2*n)) (Fin (2*n)) (ZMod 2)
abbrev VV n := Fin (2*n) → (ZMod 2)

abbrev V2 := VV 1

local notation "GL2" => ((Fin 2) → F) ≃ₗ[F] ((Fin 2) → F)

#eval FinEnum.toList $ GL2

abbrev B : MM 1 := !![0,1;1,1]

#eval (LinearEquiv.toGL'.symm ⟨!![0, 1; 1, 0],by decide⟩ : GL2)
#eval FinEnum.toList (Matrix (Fin 2) (Fin 2) F)
#eval FinEnum.toList (V2 →ₗ[F]V2)

example : FinEnum.toList (V2 →ₗ[F]V2) =[!![0, 0; 0, 0].toLin',
 !![0, 0; 0, 1].toLin',
 !![0, 0; 1, 0].toLin',
 !![0, 0; 1, 1].toLin',
 !![0, 1; 0, 0].toLin',
 !![0, 1; 0, 1].toLin',
 !![0, 1; 1, 0].toLin',
 !![0, 1; 1, 1].toLin',
 !![1, 0; 0, 0].toLin',
 !![1, 0; 0, 1].toLin',
 !![1, 0; 1, 0].toLin',
 !![1, 0; 1, 1].toLin',
 !![1, 1; 0, 0].toLin',
 !![1, 1; 0, 1].toLin',
 !![1, 1; 1, 0].toLin',
 !![1, 1; 1, 1].toLin'] := by decide

#eval FinEnum.toList ((Fin 2→ F) →ₗ[F](Fin 2 → F))


#eval FinEnum.toList (LinearMap.BilinForm F V2)

example : FinEnum.toList (LinearMap.BilinForm F V2)= [(!![0, 0; 0, 0]).toBilin',
 (!![0, 0; 0, 1]).toBilin',
 (!![0, 0; 1, 0]).toBilin',
 (!![0, 0; 1, 1]).toBilin',
 (!![0, 1; 0, 0]).toBilin',
 (!![0, 1; 0, 1]).toBilin',
 (!![0, 1; 1, 0]).toBilin',
 (!![0, 1; 1, 1]).toBilin',
 (!![1, 0; 0, 0]).toBilin',
 (!![1, 0; 0, 1]).toBilin',
 (!![1, 0; 1, 0]).toBilin',
 (!![1, 0; 1, 1]).toBilin',
 (!![1, 1; 0, 0]).toBilin',
 (!![1, 1; 0, 1]).toBilin',
 (!![1, 1; 1, 0]).toBilin',
 (!![1, 1; 1, 1]).toBilin']
 := by decide

end test

end
