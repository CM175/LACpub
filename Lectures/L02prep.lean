/-
Languages and Computation (COMP2012) 25-26
L02 : Languages
-/

import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Nat.ModEq

section Basic

class Alphabet (Sigma : Type) : Type where
  (fintype : Fintype Sigma)
  (decEq   : DecidableEq Sigma)

attribute [instance] Alphabet.fintype Alphabet.decEq

instance (Sigma : Type) [Fintype Sigma] [DecidableEq Sigma] : Alphabet Sigma :=
  ⟨inferInstance, inferInstance⟩

variable (Sigma : Type)[Alphabet Sigma]

abbrev Word := List Sigma

abbrev Lang : Type :=  Set (Word Sigma)
-- Set A = A → Prop
-- #check Set Set

instance : HPow Sigma ℕ (Word Sigma)
where hPow := λ x n ↦ List.replicate n x

end Basic

namespace Examples

inductive SigmaABC : Type
| a | b | c
deriving Fintype, DecidableEq

open SigmaABC

instance : Repr SigmaABC where
  reprPrec x _ :=
    match x with
    | a => "a"
    | b => "b"
    | c => "c"

example : Alphabet SigmaABC := by
  infer_instance

abbrev SigmaBin : Type
:= Fin 2

example : Alphabet SigmaBin := by
  infer_instance

#check ([a,b] : Word SigmaABC)
#check (a^3 : Word SigmaABC)
#eval (a^3 ++ b^3 : Word SigmaABC)
#eval ([a,a,b,c].count a)
#eval (List.count a [a,a,b,c])

abbrev aeqb : Lang SigmaABC
:= { w : Word SigmaABC | w.count a = w.count b}

abbrev aeqb' : Lang SigmaABC
| w => w.count a = w.count b

variable (Sigma : Type)[Alphabet Sigma]
variable (L : Lang Sigma)
variable (w : Word Sigma)

#check (w ∈ L)
#check (L w)

example : [a,b] ∈ aeqb := by simp
example : [a,a,b,c] ∉ aeqb := by simp

example : [] ∈ aeqb := by simp
example : [a,a,a,b] ∉ aeqb := by simp

abbrev anbm : Lang SigmaABC
:= { a^m ++ b^n | (m : ℕ)(n : ℕ)}

abbrev anbm' : Lang SigmaABC
| w => ∃ m n : ℕ, w = a^m ++ b^n

example : [a,a,b] ∈ anbm := by
  use 2 , 1
  rfl

example : [b,a,a] ∉ anbm := by sorry

def val : Word SigmaBin → ℕ
| []       => 0
| (x :: xs) => x + 2 * val xs

#eval val [0, 1, 1]  -- Output: 6

#eval val [1, 0, 1]

abbrev div3 : Lang SigmaBin
:= { w | val w ≡ 0 [MOD 3]}
-- ANCHOR_END: div3

example : [0, 1, 1] ∈ div3 :=
    by simp  [val,Nat.ModEq];

example : [1, 0, 1] ∉ div3 :=
    by simp  [val,Nat.ModEq];


#check ({[a],[a,a],[a,a,a]}: Finset (Word SigmaABC))

#eval ({1,2,2,3} = ({3,2,1} : Finset ℕ))

def a3 : Lang SigmaABC
:= {[a],[a,a],[a,a,a]}

def a3' : Lang SigmaABC
| w => w=[a] ∨ w=[a,a] ∨ w=[a,a,a]
-- ANCHOR_END: a3_pred

end Examples
