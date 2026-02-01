/-
Languages and Computation (COMP2012) 25-26
L02 : Languages

What is a languages? A language is a set of words
What is a word ? A word is a sequence of symbols
What is a symbol? An element of an alphabet
What is an alphabet? A finite type with a decidable equality.

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

abbrev Word : Type := List Sigma

abbrev Lang : Type := Set (Word Sigma)
-- Set A = A → Prop
-- Cantor
-- Set theory : Set = Set → Prop, axiomatic set theory
-- youtube : aboutLogic

-- a^3 = [a,a,a]
instance : HPow Sigma ℕ (Word Sigma)
where hPow := λ x n ↦ List.replicate n x

end Basic

#check Word

namespace Examples

inductive SigmaABC : Type where
| a | b | c
deriving Fintype, DecidableEq

open SigmaABC

abbrev SigmaBin : Type
:= Fin 2 -- {0 , 1}

#check Char

#check a

#check ([a,b,c] : Word SigmaABC) -- abc
#check ([0,0,1] : Word SigmaBin) -- 001
#check (['a','x'] : Word Char)  -- ax

#eval [a,a,b,b,c].count a
#eval [a,a,b,b,c].count b
#check (a^3 : Word SigmaABC)


-- language of words over SigmaABC
-- with the same number of a and b

abbrev aeqb : Lang SigmaABC
:= { w : Word SigmaABC | w.count a = w.count b}
-- set comprehension

abbrev aeqb' : Lang SigmaABC
| w => w.count a = w.count b

example : [a,b,a,b] ∈ aeqb := by rfl
example : (aeqb [a,b,a,b]) := by rfl
-- w ∈ L means L w
example : [a,b,b] ∉ aeqb := by simp
-- ¬ (aeqb [a,b,b])

-- words are of the form aaabb
abbrev anbm  : Lang SigmaABC
:= { a^n ++ b^m | (n : ℕ)(m : ℕ) }
abbrev anbm' : Lang SigmaABC
| w => ∃ n m : ℕ , w = a^n ++ b^m

example : [a,a,b,b] ∈ anbm := by
  use 2
  use 2
  rfl

example : [a,b,c] ∉ anbm := by sorry

-- div3 = language of binary words divisible by 3

def val : Word SigmaBin → ℕ
| []       => 0
| (x :: xs) => x + 2 * val xs
-- ANCHOR_END: val
-- this is little endian

#eval val [0, 1, 1]  -- Output: 6

#eval val [1, 0, 1]

-- ANCHOR: div3
abbrev div3 : Lang SigmaBin
:= { w | val w ≡ 0 [MOD 3]}
-- ANCHOR_END: div3

example : [0,1,1] ∈ div3 := sorry
example : [1,0,1] ∉ div3 := sorry

abbrev L1 : Lang SigmaABC
:= { [a] , [a,a] , [a,a,a]}

abbrev L1' : Lang SigmaABC
| w => w=[a] ∨ w=[a,a] ∨ w =[a,a,a]

#check ({ [a] , [a,a] , [a,a,a]} : Finset (Word SigmaABC))
-- Finset = List but identify lists with the same lements

#eval ([0,1,1] = [1,0])
#eval ({1,2,2,3} = ({3,2,1} : Finset ℕ)) -- fixed
-- coercion Finset → Set

end Examples
