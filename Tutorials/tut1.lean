import Lectures.L03

open Examples
open SigmaABC

--- ⋅

-- A language is a set of words
-- A word is a sequence of symbols of an alphabet
-- An alphabet is a finite type with decidable equality

-- Operations on languages:
-- Union (∪)
-- L₁ ∪ L₂ := { w | w ∈ L₁ ∨ w ∈ L₂}
-- [b] ∈ L₁ ∪ L₂? y
-- [a] ∈ L₁ ∪ L₂? y
-- Intersection (∩)
-- L₁ ∩ L₂ := { w | w ∈ L₁ ∧ w ∈ L₂}
-- [b] ∈ L₁ ∩ L₂? y
-- [a] ∈ L₁ ∩ L₂? n
-- Concatenation (⋅)
-- L₁ ⋅ L₂ := { w ++ v | w ∈ L₁, v ∈ L₂}
-- [b,b] ∈ L₁ ⋅ L₂? y
-- [a,b] ∈ L₁ ⋅ L₂? y
-- [b] ∈ L₁ ⋅ L₂? y
-- [b,a] ∈ L₁ ⋅ L₂? n
-- L₁ ⋅ L₂ := {[b], [b,c],[a,b],[a,b,c],[b,b],[b,b,c]}

-- Kleene Star (*)
-- L₁* := {w₁ ++ w₂ ++ ... ++ wₙ | n ∈ ℕ , w₁,w₂,...,wₙ ∈ L₁}
-- [a,b] ∈ L₁*? y
-- [a,a] ∈ L₁*? y
-- [b] ∈ L₁*? y
-- [] ∈ L₂*? y

-- For which 2 languages L is L* finite?
def L₃ : Lang SigmaABC := ∅
-- L₃* = ∅

def L₄ : Lang SigmaABC := {[]}
-- L₄* = {[]}

-- What is (L₁ ∩ L₂)*?
-- It is {[], [b],[b,b],[b,b,b],...}

def L₁ : Lang SigmaABC
:= { [], [a], [b]}

def L₂ : Lang SigmaABC
:= { [b], [b,c]}

#check (L₁ : Lang SigmaABC)
