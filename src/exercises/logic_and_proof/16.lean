/-
1. Fill in the sorry’s in the last three proofs below.
-/
import data.set

section ex1

open function int algebra

def f (x : ℤ) : ℤ := x + 3
def g (x : ℤ) : ℤ := -x
def h (x : ℤ) : ℤ := 2 * x + 3

example : injective f :=
assume x1 x2,
assume h1 : x1 + 3 = x2 + 3,   -- Lean knows this is the same as f x1 = f x2
show x1 = x2, from eq_of_add_eq_add_right h1

example : surjective f :=
assume y,
have h1 : f (y - 3) = y, from calc
  f (y - 3) = (y - 3) + 3 : rfl
        ... = y           : by rw sub_add_cancel,
show ∃ x, f x = y, from exists.intro (y - 3) h1

example (x y : ℤ) (h : 2 * x = 2 * y) : x = y :=
have h1 : 2 ≠ (0 : ℤ), from dec_trivial,  -- this tells Lean to figure it out itself
show x = y, from eq_of_mul_eq_mul_left h1 h

example (x : ℤ) : -(-x) = x := neg_neg x

example (A B : Type) (u : A → B) (v : B → A) (h : left_inverse u v) :
  ∀ x, u (v x) = x :=
h

example (A B : Type) (u : A → B) (v : B → A) (h : left_inverse u v) :
  right_inverse v u :=
h

-- fill in the sorry's in the following proofs

example : injective h :=
assume x y : ℤ,
assume q : 2 * x + 3 = 2 * y + 3,
have h : 2 * x = 2 * y, from
  calc 2 * x = (2 * x + 3) - 3 : by simp
         ... = (2 * y + 3) - 3 : by rw q
         ... = 2 * y           : by simp,
have h1 : 2 ≠ (0 : ℤ), from dec_trivial,
show x = y, from eq_of_mul_eq_mul_left h1 h

example : surjective g :=
assume y,
have h1 : g (-y) = y, from calc
  g (-y) = -(-y) : rfl
     ... = y     : neg_neg y,
show ∃ x, g x = y, from ⟨-y, h1⟩

example (A B : Type) (u : A → B) (v1 : B → A) (v2 : B → A)
  (h1 : left_inverse v1 u) (h2 : right_inverse v2 u) : v1 = v2 :=
funext
  (assume x,
    calc
      v1 x = v1 (u (v2 x)) : by rw h2
       ... = v2 x          : by rw h1)

end ex1

/-
2. Fill in the sorry in the proof below.
-/

section ex2

open function set

variables {X Y : Type}
variable  f : X → Y
variables A B : set X

example : f '' (A ∪ B) = f '' A ∪ f '' B :=
eq_of_subset_of_subset
  (assume y,
    assume h1 : y ∈ f '' (A ∪ B),
    exists.elim h1 $
    assume x h,
    have h2 : x ∈ A ∪ B, from h.left,
    have h3 : f x = y, from h.right,
    or.elim h2
      (assume h4 : x ∈ A,
        have h5 : y ∈ f '' A, from ⟨x, h4, h3⟩,
        show y ∈ f '' A ∪ f '' B, from or.inl h5)
      (assume h4 : x ∈ B,
        have h5 : y ∈ f ''  B, from ⟨x, h4, h3⟩,
        show y ∈ f '' A ∪ f '' B, from or.inr h5))
  (assume y,
    assume h2 : y ∈ f '' A ∪ f '' B,
    or.elim h2
      (assume h3 : y ∈ f '' A,
        exists.elim h3 $
        assume x h,
        have h4 : x ∈ A, from h.left,
        have h5 : f x = y, from h.right,
        have h6 : x ∈ A ∪ B, from or.inl h4,
        show y ∈ f '' (A ∪ B), from ⟨x, h6, h5⟩)
      (assume h3 : y ∈ f '' B,
        exists.elim h3 $
        assume x h,
        have h4 : x ∈ B, from h.left,
        have h5 : f x = y, from h.right,
        have h6 : x ∈ A ∪ B, from or.inr h4,
        show y ∈ f '' (A ∪ B), from ⟨x, h6, h5⟩))

-- remember, x ∈ A ∩ B is the same as x ∈ A ∧ x ∈ B
example (x : X) (h1 : x ∈ A) (h2 : x ∈ B) : x ∈ A ∩ B :=
and.intro h1 h2

example (x : X) (h1 : x ∈ A ∩ B) : x ∈ A :=
and.left h1

-- Fill in the proof below.
-- (It should take about 8 lines.)

example : f '' (A ∩ B) ⊆ f '' A ∩ f '' B :=
assume y,
assume h1 : y ∈ f '' (A ∩ B),
show y ∈ f '' A ∩ f '' B, from (
  exists.elim h1 $
  assume (x : X) (h : x ∈ A ∩ B ∧ f x = y),
  have ha : x ∈ A, from h.left.left,
  have hb : x ∈ B, from h.left.right,
  have he : f x = y, from h.right,
  show y ∈ f '' A ∩ f '' B, from ⟨⟨x, ha, he⟩, ⟨x, hb, he⟩⟩
)

end ex2