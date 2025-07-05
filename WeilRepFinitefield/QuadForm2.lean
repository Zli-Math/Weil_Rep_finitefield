import Mathlib
import WeilRepFinitefield.Compute

variable (F: Type*) [CommSemiring F] (n : ℕ)

abbrev QuadForm := {B : Matrix (Fin n) (Fin n) F // ∀ i j , j > i →  B i j = 0}


variable {F n}

namespace QuadForm
section quadNotation

abbrev _root_.Matrix.toQuadForm [DecidableEq F] : Matrix (Fin n) (Fin n) F  → QuadForm F n :=
  fun B =>
    if H : ∀ i j, j > i → B i j = 0 then
     ⟨B, H⟩
    else
      ⟨0, by simp⟩

syntax (name := quadNotation) "!QF" term  : term

macro_rules
  | `(!QF $term:term) => `(Matrix.toQuadForm $term )


@[app_unexpander Matrix.toQuadForm]
def quadSnocUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term ) => `(!QF $term)
  | _ => throw ()


instance hasRepr [Repr F] : Repr (QuadForm F n) where
  reprPrec f _ := "(!QF " ++ repr f.1 ++ ")"



end quadNotation




section toQuadraticForm

abbrev toQuadraticForm (B : QuadForm F n) : QuadraticForm F (Fin n → F)
:= B.1.toBilin'.toQuadraticMap

variable {F : Type*} [CommRing F] [DecidableEq F] {n :ℕ}

private abbrev pure (i : Fin n) : Fin n → F := Function.update 0 i 1

abbrev _root_.QuadraticForm.toQuadForm (f: QuadraticForm F (Fin n → F)) : QuadForm F n := ⟨
    fun i j =>
      if H : j > i then 0 else
        if H': j = i then f (Function.update 0 i 1)
        else
          let MM := LinearMap.BilinForm.toMatrix' (f.polarBilin : LinearMap.BilinForm F (Fin n → F))
          MM i j
    ,
    by
      intro i j Hij
      simp [Hij]
    ⟩


def equivQuadraticForm : (QuadForm F n) ≃ (QuadraticForm F (Fin n → F)) where
  toFun := toQuadraticForm
  invFun := QuadraticForm.toQuadForm
  left_inv := by
    intro f
    sorry
  right_inv := by
    intro f
    sorry

end toQuadraticForm


section test
abbrev Q0 : QuadForm (ZMod 2) 0 := !QF!![]
abbrev Q1 : QuadForm (ZMod 2) 1 := !QF!![0]
abbrev Q1' : QuadForm (ZMod 2) 2:= !QF!![1,0;1,1]
abbrev Q1'' : QuadForm (ZMod 2) 3:= !QF!![0,0,0;0,1,0;1,0,0]

#eval Q1
#eval Q1'
#eval Q1''
#eval! FinEnum.toList (QuadraticForm (ZMod 2) (Fin 2 → ZMod 2))



open Lean Qq
example : (Fin 2) = (ZMod 2) := rfl
--#eval   Lean.toExpr Q1''
--#eval  (by_elabq return Lean.toExpr Q1'') = Q1''
#eval  (Finset.univ : Finset $ QuadForm (ZMod 2) 3).card
#eval (Finset.univ : Finset (Fin 2 → (ZMod 2)))
---#eval (!#[![0],![1,0]] : QuadForm (ZMod 2) 2)

end test

end QuadForm
