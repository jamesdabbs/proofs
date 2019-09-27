/-
Exercises from https://leanprover.github.io/logic_and_proof

Chapter 12. Sets in Lean
-/

import data.set

-- 1
section
  variable U : Type
  variables A B C : set U

  example : ∀ x, x ∈ A ∩ C → x ∈ A ∪ B :=
  assume x,
  assume : x ∈ A ∩ C,
  have x ∈ A, from this.left,
  show x ∈ A ∪ B, from or.inl this

  example : ∀ x, x ∈ -(A ∪ B) → x ∈ -A :=
  assume x,
  assume : x ∈ -(A ∪ B),
  have np : x ∉ A ∪ B, from this,
  assume : x ∈ A,
  have p : x ∈ A ∪ B, from or.inl this,
  absurd p np
end

-- 2
section

open set

variable {U : Type}

/- defining "disjoint" -/

def disj (A B : set U) : Prop := ∀ ⦃x⦄, x ∈ A → x ∈ B → false

example (A B : set U) (h : ∀ x, ¬ (x ∈ A ∧ x ∈ B)) :
  disj A B :=
assume x,
assume h1 : x ∈ A,
assume h2 : x ∈ B,
have h3 : x ∈ A ∧ x ∈ B, from and.intro h1 h2,
show false, from h x h3

-- notice that we do not have to mention x when applying
--   h : disj A B
example (A B : set U) (h1 : disj A B) (x : U)
    (h2 : x ∈ A) (h3 : x ∈ B) :
  false :=
h1 h2 h3

-- the same is true of ⊆
example (A B : set U) (x : U) (h : A ⊆ B) (h1 : x ∈ A) :
  x ∈ B :=
h h1

example (A B C D : set U) (h1 : disj A B) (h2 : C ⊆ A)
    (h3 : D ⊆ B) :
  disj C D :=
assume x,
assume c : x ∈ C,
have a : x ∈ A, from h2 c,
assume d : x ∈ D,
have b : x ∈ B, from h3 d,
h1 a b

end

-- 3
section

open set

variables {I U : Type}
variables (A : I → set U) (B : I → set U) (C : set U)

example : (⋂ i, A i) ∩ (⋂ i, B i) ⊆ (⋂ i, A i ∩ B i) :=
assume x,
assume h : x ∈ (⋂ i, A i) ∩ (⋂ i, B i),
show x ∈ ⋂ i, A i ∩ B i, by simp * at *

example : C ∩ (⋃ i, A i) ⊆ ⋃i, C ∩ A i :=
assume x,
assume h : x ∈ C ∩ (⋃ i, A i),
show x ∈ ⋃ i, C ∩ A i, by simp * at *

end

-- 4
section

open set

variable  {U : Type}
variables A B C : set U

example (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := subset.trans h1 h2
example : A ⊆ A := subset.refl A

example (h : A ⊆ B) : powerset A ⊆ powerset B :=
assume p,
assume : p ∈ 𝒫 A,
have p ⊆ A, from this,
have p ⊆ B, from subset.trans this h,
show p ∈ 𝒫 B, from this

example (h : powerset A ⊆ powerset B) : A ⊆ B :=
have A ∈ 𝒫 A, from subset.refl A,
have A ∈ 𝒫 B, from (h this),
show A ⊆ B, from this

end