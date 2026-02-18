/-
  Tutorial 1: Languages, Words, and Operations
  Course: Language and Computation (COMP2012)
  TA: Aref Mohammadzadeh
  Date: 05 February 2026
-/

import Proofs.Lang
import Mathlib.Data.Fintype.Basic

open Lang
open Examples
open SigmaABC
open Nat
/-!
  ### RECAP OF DEFINITIONS
  1. Words & Languages:
     - An alphabet `Sigma` is a finite set with decidable equality.

          definition in Lean:
          variable (Sigma : Type)
          [Fintype Sigma][DecidableEq Sigma]

          example:
          inductive SigmaABC : Type
          | a | b | c

     - A `Word Sigma` is a list over `Sigma` . The empty word ε is `[]`.

          definition in Lean:
          abbrev Word := List Sigma

          example:
          [a,b,a] : Word SigmaABC

     - A `Lang Sigma` is a (possibily infinte set of words `Set (Word Sigma)`.

         definition in Lean@
         abbrev Lang : Type
        := Set (Word Sigma)

        example:
        ({[a] , [a,b,c]} : Lang SigmaABC)


  2. Concatenation (L1 ⬝ L2):
     A word `w` is in `L1 ⬝ L2` if there exist `w1 ∈ L1` and `w2 ∈ L2`
     such that `w = w1 ++ w2`.
     In Lean: `inductive append ... | l_app' : w1 ∈ l1 → w2 ∈ l2 → (w1 ++ w2) ∈ l1 ⬝ l2`

 3. Kleene Star (L*):
     - Base: `l_star_nil : [] ∈ L*`
     - Step: `l_star_app : w1 ∈ L → w2 ∈ L* → (w1 ++ w2) ∈ L*`

  4. These two languages are different!:
     - The Empty Language: `{}` (contains no words).
     - The Unit Language: `{[]}` (contains only the empty word).
-/
variable {Sigma : Type}
  [Fintype Sigma][DecidableEq Sigma]

inductive append (l1 l2 : Lang Sigma) : Lang Sigma
  | l_app' : ∀ w1 w2 : Word Sigma ,
      w1 ∈ l1 → w2 ∈ l2 → append l1 l2 (w1 ++ w2)

infix:70 " ⬝ " => append

def l_app : ∀ {l1 l2 : Lang Sigma},
          ∀ w1 w2 : Word Sigma ,

        w1 ∈ l1
      → w2 ∈ l2
      ----------------------
      → (w1 ++ w2) ∈ l1 ⬝ l2

      := append.l_app'

inductive star' (l1 : Lang Sigma) : Lang Sigma
  | l_star_nil' : star' l1 []
  | l_star_app' : ∀ w1 w2 : Word Sigma ,
      w1 ∈ l1 → star' l1 w2 → star' l1 (w1 ++ w2)

postfix:100 " *' " => star'

variable {l1 : Lang Sigma}

def l_star_nil :

  -----------
  [] ∈ l1 *'

  := star'.l_star_nil'

def l_star_app : ∀ w1 w2 : Word Sigma ,

         w1 ∈ l1
       → w2 ∈ l1 *'
       ------------------
       → w1 ++ w2 ∈ l1 *'

  := star'.l_star_app'




namespace Tutorial1


def La : Lang SigmaABC := { [a], [a, b] }
def Lb : Lang SigmaABC := { [b], [] }
def Lc : Lang SigmaABC := { [b] , [c]}

/-
  Exercise 1: Finite Language Enumeration
  Find the set of all words in L_ex1.
  Logic: Words of length exactly 2 containing 'b'.
-/
def L_ex1 : Lang SigmaABC :=
  { w | w.length = 2 ∧ b ∈ w }

def L_ex1_enum : Finset (Word SigmaABC) :=
  {[a,b]}


-- Exercise 2: Operations on Languages
-- 2a.
def L_2a : Lang SigmaABC := (La ⬝Lc) ∩ { w | w.length = 2 }

def L_2a_enum : Finset (Word SigmaABC) :=
{[a, b], [a, c]}
-- 2b. Nested Operations: (L1 ∪ L2) concatenated with (L1 ∩ L2)
-- Logic: ( {a, ab, b, ε} ) ⬝ ( {b, ε} ∩ {a, ab} )
-- Since Lb ∩ La = ∅, this should be empty!
def L_2b : Lang SigmaABC := (La ∪ Lb) ⬝(Lb ∩ La)

def L_2b_enum : Finset (Word SigmaABC) :=
  {}

-- 2c. Concatenation of three languages: (La ⬝ Lb) ⬝ Lc
-- Logic: {a, ab} ⬝ {b, ε} ⬝ {b, c}
def L_2c : Lang SigmaABC := (La ⬝Lb) ⬝Lc

def L_2c_enum : Finset (Word SigmaABC) :=
{ [a,b], [a, b,b], [a, b, b,b],    [a,c], [a, b,c], [a, b, b,c] }

example : L_2a = L_2a_enum := by sorry
example : L_2b = L_2b_enum := by sorry
example : L_2c = L_2c_enum := by sorry



/-
  Exercise 3: List all words in {[a, a] , [b]}* with length less than or equal to 3.
-/
def L_star_limit : Lang SigmaABC :=
sorry
def L_star_limit_enum : Finset (Word SigmaABC) :=
{[], [a,a], [b], [b,a,a], [a,a,b], [b,b], [b,b,b]}

/-! Exercise 4: MEMBERSHIP PROOFS -/

-- For concatenation, we use `apply l_app` and provide the two parts of the word.
example : [a, b, b] ∈ La ⬝Lb := by
  apply l_app [a, b] [b]


-- For Star, we "build" the word from the head using `l_star_app`
example : [a, a] ∈ ({[a]} : Lang SigmaABC)*' := by
  apply l_star_app [a]
  


/-
  Challenge!
  Exercise 5: Distributivity of Concatenation over Union
  Goal: Prove L1 ⬝ (L2 ∪ L3) = (L1 ⬝ L2) ∪ (L1 ⬝ L3)
-/
example (L1 L2 L3 : Lang Sigma) : L1 ⬝(L2 ∪ L3) = (L1 ⬝L2) ∪ (L1 ⬝L3) := by
  ext w  --(This line is a hint to start!)
  sorry

end Tutorial1
