import Mathlib

section

universe u

variable {α β γ : Type*} {R :Type u} [CommSemiring R]

local notation "F" => (ZMod 2)

abbrev VV n := Fin (2*n) → (ZMod 2)

abbrev V2 := VV 1

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
  reprPrec := fun v _ => repr v.toMatrix'++".toLin'"

/-
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

-/


end
