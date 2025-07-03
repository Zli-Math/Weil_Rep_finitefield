import Mathlib

variable (F: Type*) [Ring F] (n : ℕ)

abbrev QuadForm := (i :Fin n) → Fin (i+1) → F

namespace QuadForm

variable {F n} in

abbrev quadEmpty : QuadForm F 0 := by
  intro i
  have := i.2
  contradiction

variable {F n} in
abbrev quadSnoc (f : QuadForm F n) (v : (Fin (n+1) → F)) : QuadForm F (n+1):= Fin.snoc f v


section quadNotation

syntax (name := quadNotation) "!#[" term,* "]" : term

macro_rules
  | `(!#[$term0:term, $terms:term,*, $term:term]) => `(quadSnoc !#[$term0,$terms,*] $term )
  | `(!#[$term:term, $term1:term]) => `(quadSnoc !#[$term] $term1 )
  | `(!#[$term:term]) => `(quadSnoc quadEmpty $term )
  | `(!#[]) => `(quadEmpty)


@[app_unexpander quadSnoc]
def quadSnocUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ !#[$term0, $terms,*] $term1 ) => `(!#[$term0, $terms,*, $term1])
  | `($_ !#[$term0] $term1 ) => `(!#[$term0, $term1])
  | `($_ !#[] $term ) => `(!#[$term])
  | _ => throw ()

/-- Unexpander for the `![]` notation. -/
@[app_unexpander quadEmpty]
def quadEmptyUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_:ident) => `(!#[])
  | _ => throw ()


instance hasRepr [Repr F] : Repr (QuadForm F n) where
  reprPrec f _ :=
    Std.Format.bracket "!#[" (Std.Format.joinSep
      ((List.finRange n).map fun n => repr (f n)) ("," ++ Std.Format.line)) "]"




open Lean Qq in
def mkLiteralQ {u : Level} {F : Q(Type u)} {n : ℕ} (elems : (i : Fin n) → Q(Fin ($i+1) → $F)) :
    Q(QuadForm $F $n) :=
    match n with
    | 0 => q(quadEmpty)
    | n+1 =>
      let elems' := Fin.init elems
      let init := mkLiteralQ elems'
      let last := elems (Fin.last n)
      q(quadSnoc $init $last)

/-
-- The code works for Lean 4.22
open Lean Qq Matrix in
protected instance toExpr {F : Type u} [ToLevel.{u}] [ToExpr F] (n : ℕ) : ToExpr (QuadForm F n) :=
  have lu := toLevel.{u}
  have eF : Q(Type $lu) := toTypeExpr F
  let toTypeExpr := q(QuadForm $eF $n)
  { toTypeExpr, toExpr v := mkLiteralQ (F:=eF) (fun i => toExpr (v i)) }
-/

open Lean Qq Matrix in
protected instance _root_.ZMod.instToExpr (n : ℕ) : ToExpr (ZMod n) :=
  match n with
  | 0 => by
    rw [ZMod] at *
    infer_instance
  | n+1 => by
    rw [ZMod] at *
    infer_instance

end quadNotation

section evaluation

variable {F n}

abbrev eval (f : QuadForm F n) (w : Fin n → F) : F :=
  ∑ (i : Fin n), ∑ (j : Fin (i+1)), f i j * w i * w ⟨j, by linarith [i.2,j.2]⟩

--#print eval._proof_1

end evaluation


section test
abbrev Q0 : QuadForm (ZMod 2) 0 := !#[]
abbrev Q1 : QuadForm (ZMod 2) 1 := !#[![0]]
abbrev Q1' : QuadForm (ZMod 2) 2:= !#[![0],![1,0]]
abbrev Q1'' : QuadForm (ZMod 2) 3:= !#[![0],![1,0],![1,0,0]]
abbrev Q1''' : QuadForm (ZMod 2) 4:= !#[![0],![1,0],![1,0,0],![1,2,3,4]]

open Lean Qq
example : (Fin 2) = (ZMod 2) := rfl
--#eval   Lean.toExpr Q1''
--#eval  (by_elabq return Lean.toExpr Q1'') = Q1''
#eval  (Finset.univ : Finset $ QuadForm (ZMod 2) 2)
#eval (Finset.univ : Finset (Fin 2 → (ZMod 2)))
---#eval (!#[![0],![1,0]] : QuadForm (ZMod 2) 2)

end test
end QuadForm
