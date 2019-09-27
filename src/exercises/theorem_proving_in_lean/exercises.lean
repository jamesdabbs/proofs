-- Chapter 2
namespace ch2

/-
1. Define the function Do_Twice
-/
def Do_Twice (f: ℕ → ℕ) (n : ℕ) : ℕ := f (f n)

#check Do_Twice
#reduce Do_Twice (λ x, x * 3) 2

/-
2. Define the functions curry and uncurry
-/

def curry (f : ℕ × ℕ → ℕ) (a b : ℕ) : ℕ := f (a, b)
def uncurry (f : ℕ → ℕ → ℕ) (c : ℕ × ℕ) : ℕ := f c.1 c.2

/-
3. Above, we used the example vec α n for vectors of elements of type α of
length n. Declare a constant vec_add that could represent a function that adds
two vectors of natural numbers of the same length, and a constant vec_reverse
that can represent a function that reverses its argument. Use implicit arguments
for parameters that can be inferred. Declare some variables and check some
expressions involving the constants that you have declared.
-/

universe u
variables {α : Type u} {n m o : ℕ}

constant vector : Type u → ℕ -> Type u

namespace vector
  constant empty : vector α 0
  constant cons : α → vector α n → vector α (n + 1)

  #check empty
  #check cons 1 empty
  #check (cons 5 (cons 10 (cons 3 (empty))))

  constant add : vector α n → vector α m -> vector α (n + m)
  #check add (cons 1 (cons 2 (empty))) (cons 3 (empty))

  constant reverse : vector α n → vector α n
  #check reverse (cons 1 (cons 2 (empty)))
end vector

/-
4. Similarly, declare a constant matrix so that matrix α m n could
represent the type of m by n matrices. Declare some constants to
represent functions on this type, such as matrix addition and
multiplication, and (using vec) multiplication of a matrix by a
vector. Once again, declare some variables and check some
expressions involving the constants that you have declared.
-/

constant matrix : Type u → ℕ → ℕ → Type u

namespace matrix
end matrix
  constant add : matrix α n m → matrix α n m → matrix α n m
  constant mult : matrix α n m → matrix α m o → matrix α n o
end ch2

-- Chapter 3
namespace ch3
/-
1. Prove as many identities from the previous section as you can, replacing the “sorry” placeholders with actual proofs.
-/
universe u
variables p q r s : Prop

def id {α : Type u} (a : α) : α := a

-- Explicit (de)structuring
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
iff.intro
  (assume h : (p ∧ q) ∧ r,
    show p ∧ (q ∧ r), from
      and.intro
        (and.left (and.left h))
        (and.intro
          (and.right (and.left h))
          (and.right h)))
  (assume h : p ∧ (q ∧ r),
    show (p ∧ q) ∧ r, from
      and.intro
        (and.intro
          (and.left h)
          (and.left (and.right h)))
        (and.right (and.right h)))

#check @or.inr

-- Alternate form
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
iff.intro
  (λ h, ⟨h.left.left, h.left.right, h.right⟩)
  (λ h, ⟨⟨h.left, h.right.left⟩, h.right.right⟩)

#check p ∨ (q ∨ r)

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
iff.intro
  (assume h : (p ∨ q) ∨ r,
    h.elim (λ i, i.elim or.inl (or.inr ∘ or.inl)) (or.inr ∘ or.inr))
  (assume h : p ∨ (q ∨ r),
    h.elim (or.inl ∘ or.inl) (λ i, i.elim (or.inl ∘ or.inr) or.inr))

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
iff.intro
  (λ h, h.elim (λ i, i.elim or.inl (or.inr ∘ or.inl)) (or.inr ∘ or.inr))
  (λ h, h.elim (or.inl ∘ or.inl) (λ i, i.elim (or.inl ∘ or.inr) or.inr))

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
iff.intro
  (assume h : p ∧ (q ∨ r),
    have hp : p, from and.left h,
    have hqr : q ∨ r, from and.right h,
    show (p ∧ q) ∨ (p ∧ r),
      from hqr.elim (assume hq : q, or.inl ⟨hp, hq⟩)
                    (assume hr : r, or.inr ⟨hp, hr⟩))
  (assume h : (p ∧ q) ∨ (p ∧ r),
    show p ∧ (q ∨ r), from
    h.elim
      (assume i : p ∧ q, ⟨and.left i, or.inl (and.right i)⟩)
      (assume i : p ∧ r, ⟨and.left i, or.inr (and.right i)⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
iff.intro
  (assume h : p ∨ (q ∧ r), h.elim (λ p, ⟨or.inl p, or.inl p⟩) (λ qr, ⟨or.inr (and.left qr), or.inr (and.right qr)⟩))
  (assume h : (p ∨ q) ∧ (p ∨ r),
    h.left.elim or.inl (λ q', h.right.elim or.inl (λ r', or.inr ⟨q', r'⟩)))

example: (p → (q → r)) ↔ (p ∧ q → r) :=
iff.intro
  (assume f, λ p, f p.1 p.2)
  (assume g, λ a, λ b, g ⟨a, b⟩)

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
iff.intro
  (assume f, ⟨f ∘ or.inl, f ∘ or.inr⟩)
  (assume h, λ pq, pq.elim h.left h.right)

example: ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
iff.intro
  (assume npq : ¬(p ∨ q), ⟨npq ∘ or.inl, npq ∘ or.inr⟩)
  (assume h : ¬p ∧ ¬q, assume pq, pq.elim h.left h.right)

example: ¬p ∨ ¬q → ¬(p ∧ q) :=
assume h : ¬p ∨ ¬q,
assume pq : p ∧ q,
h.elim (λ np, np pq.left) (λ nq, nq pq.right)

example : ¬(p ∧ ¬p) := λ h, absurd h.left h.right

example: p ∧ ¬q → ¬(p → q) := λ pnq h, absurd (h pnq.left) pnq.right

example: ¬p → (p → q) := λ np p, absurd p np

example: (¬p ∨ q) → (p → q) :=
  assume npq : ¬p ∨ q,
  assume hp : p,
  npq.elim (absurd hp) (λ q, q)

example : p ∨ false ↔ p :=
iff.intro
  (λ h, h.elim (λ p, p) false.elim)
  or.inl

example : p ∧ false ↔ false :=
iff.intro and.right false.elim

example : (p → q) → (¬q → ¬p) := λ pq nq, nq ∘ pq

namespace with_classical
open classical

example : ¬(p ↔ ¬p) :=
assume h : p ↔ ¬p,
(em p).elim
  (λ p, h.mp p p)
  (λ np, absurd (h.mpr np) np)

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
assume f,
(em r).elim
  (λ r, or.inl (λ _, r))
  (λ nr, or.inr (λ p, (f p).elim (λ r, absurd r nr) (λ s, s)))

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
assume npq : ¬(p ∧ q),
(em p).elim (λ hp, (em q).elim (λ hq, absurd (and.intro hp hq) npq) or.inr) or.inl

example : ¬(p → q) → p ∧ ¬q :=
assume npq : ¬(p → q),
(em p).elim
  -- (λ p, ⟨p, λ q, npq (λ _, q)⟩)
  (assume hp : p,
    have nq : ¬q, from (λ q', npq (λ _, q')),
    show p ∧ ¬q, from ⟨hp, nq⟩)
  (assume hnp : ¬p,
    have pq : p → q, from (λ p, absurd p hnp),
    absurd pq npq)

example : (p → q) → (¬p ∨ q) :=
(em p).elim
  (λ p pq, or.inr (pq p))
  (λ np _, or.inl np)

example : (¬q → ¬p) → (p → q) :=
(em q).elim
  (λ q _ _, q)
  (λ nq nqp p, absurd p (nqp nq))

example : p ∨ ¬p := by exact (em p)

example : (((p → q) → p) → p) :=
(em q).elim
  (λ q f, f (λ _, q))
  ((em p).elim
    (λ p _ _, p)
    (λ np nq f, f (λ p', absurd p' np)))

end with_classical

/-
2. Prove ¬(p ↔ ¬p) without using classical logic.
-/

example (p : Prop): ¬(p ↔ ¬p) := by simp

-- TODO: Provide a direct proof
example (p : Prop): ¬(p ↔ ¬p) := sorry

end ch3

-- Chapter 4
namespace ch4

namespace ex1
/-
Prove these equivalences.
You should also try to understand why the reverse implication is not derivable
in the last example.
-/

variables (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
iff.intro
  (λ h, ⟨λ y, (h y).left, λ y, (h y).right⟩)
  (λ h x, ⟨h.left(x), h.right(x)⟩)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
assume pq,
assume p,
assume x : α,
show q x, from pq x (p x)

example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
λ pq p x, pq x (p x)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
λ h, h.elim (λ px x, or.inl (px x)) (λ qx x, or.inr (qx x))

end ex1

namespace ex2
/-
It is often possible to bring a component of a formula outside a universal
quantifier, when it does not depend on the quantified variable. Try proving
these (one direction of the second of these requires classical logic):
-/

variables (α : Type) (p q : α → Prop)
variable r : Prop

example : α → ((∀ x: α, r) ↔ r) :=
λ y, iff.intro (λ f, f y) (λ r _, r)

open classical
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
iff.intro
  -- This branch requires classical reasoning
  (λ h, (em r).elim or.inr
    (λ nr, or.inl (λ x, (h x).elim id (λ r, absurd r nr))))
  (λ h x, h.elim (λ px, or.inl(px x)) or.inr)

example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
iff.intro (λ f r _, f _ r) (λ f _ r, f r _)

end ex2

namespace ex3
/-
Consider the “barber paradox,” that is, the claim that in a certain town there
is a (male) barber that shaves all and only the men who do not shave themselves.
Prove that this is a contradiction:
-/
variables (men : Type) (barber : men)
variable (shaves : men → men → Prop)

open classical -- This is expedient, but not necessary; c.f. ex 3.2
example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : false :=
(em (shaves barber barber)).elim
  (assume s : shaves barber barber,
  have ns : ¬shaves barber barber, from (h barber).mp(s),
  absurd s ns)
  (assume ns : ¬shaves barber barber,
  have s : shaves barber barber, from (h barber).mpr(ns),
  absurd s ns)

end ex3

namespace ex4
/-
Below, we have put definitions of divides and even in a special namespace to
avoid conflicts with definitions in the library. The instance declaration make
it possible to use the notation m | n for divides m n. Don’t worry about how it
works; you will learn about that later.
-/
def divides (m n: ℕ) : Prop := ∃ k, m * k = n

instance : has_dvd nat := ⟨divides⟩

def even (n: ℕ) : Prop := 2 ∣ n

variables m n : ℕ

#check m ∣ n
#check m ^ n
#check even (m ^ n +3)

/-
Remember that, without any parameters, an expression of type Prop is just an
assertion. Fill in the definitions of prime and Fermat_prime below, and
construct the given assertion. For example, you can say that there are
infinitely many primes by asserting that for every natural number n, there is a
prime number greater than n. Goldbach’s weak conjecture states that every odd
number greater than 5 is the sum of three primes. Look up the definition of a
Fermat prime or any of the other statements, if necessary.
-/

def prime (n : ℕ) : Prop := ∀m, m ∣ n → m = 1 ∨ m = n

def infinitely_many_primes : Prop := ∀ n, ∃ k, k > n ∧ prime k

def Fermat_prime (n : ℕ) : Prop := ∃ k : ℕ, n = 2 ^ (2 ^ k) ∧ prime n

def infinitely_many_Fermat_primes : Prop := ∀ n, ∃ k, k > n ∧ Fermat_prime k

def goldbach_conjecture : Prop := ∀ n, ∃ p₁ p₂, n = p₁ + p₂ ∧ prime p₁ ∧ prime p₂

def Goldbach's_weak_conjecture : Prop := ∀ n, ∃ p₁ p₂ p₃, n = p₁ + p₂ + p₃ ∧ prime p₁ ∧ prime p₂

def Fermat's_last_theorem : Prop :=
  ∀ (a b c n : ℕ), a > 0 -> b > 0 -> c > 0 -> a^n + b^n = c^n -> n ≤ 2

end ex4

namespace ex5
/-
Prove as many of the identities listed in Section 4.4 as you can.
-/

variables (α : Type) (p q : α → Prop)
variable a : α
variable r : Prop

example : (∃ x : α, r) → r := λ ⟨_, hr⟩, hr

example : r → (∃ x : α, r) := λ r, exists.intro a r

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
iff.intro
  (λ ⟨x, pxar⟩, ⟨exists.intro x pxar.left, pxar.right⟩)
  (λ ⟨⟨x, px⟩, r⟩, exists.intro x ⟨px, r⟩)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
iff.intro
  (λ ⟨x, pqx⟩, pqx.elim
    (or.inl ∘ exists.intro x)
    (or.inr ∘ exists.intro x))
  (λ h, h.elim
    (λ ⟨x, px⟩, exists.intro x (or.inl px))
    (λ ⟨x, qx⟩, exists.intro x (or.inr qx)))

example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
iff.intro
  (λ nep x px, nep (exists.intro x px))
  (λ nax ⟨x, px⟩, nax x px)

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
iff.intro
  (λ apxr ⟨x, px⟩, apxr x px)
  (λ epxr _ px, epxr (exists.intro _ px))

open classical
-- TODO: do these all _require_ classical reasoning?

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
iff.intro
  (λ axpx ⟨_, npx,⟩, npx (axpx _))
  (λ nexnpx x, by_contradiction (λ npx, nexnpx (exists.intro x npx)))

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
iff.intro
  (λ ⟨_, px⟩ axnpx, axnpx _ px)
  sorry

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
iff.intro
  (λ naxpx, sorry)
  (λ ⟨_, npx⟩ axpx, npx (axpx _))

example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
iff.intro
  (λ ⟨x, pxr⟩ y, pxr(y(x)))
  sorry

example : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
iff.intro
  (λ ⟨x, rpx⟩ r, exists.intro x (rpx r))
  (λ repx, (em r).elim
    (λ hr, let ⟨x, px⟩ := repx hr in exists.intro x (λ _, px))
    (λ nr, exists.intro a (λ r, absurd r nr)))

end ex5

namespace ex6
/-
Give a calculational proof of the theorem log_mul below.
-/
variables (real : Type) [ordered_ring real]
variables (log exp : real → real)
variable log_exp_eq : ∀ x, log (exp x) = x
variable exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
variable exp_pos : ∀ x, exp x > 0
variable exp_add : ∀ x y, exp (x + y) = exp x * exp y

-- this ensures the assumptions are available in tactic proofs
include log_exp_eq exp_log_eq exp_pos exp_add

example (x y z : real) :
  exp (x + y + z) = exp x * exp y * exp z :=
by rw [exp_add, exp_add]

example (y : real) (h : y > 0) : exp (log y) = y :=
  exp_log_eq h

theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
  log (x * y) = log x + log y :=
calc log (x * y) = log (exp (log x) * y)           : by rw (exp_log_eq hx)
             ... = log (exp (log x) * exp (log y)) : by rw (exp_log_eq hy)
             ... = log (exp (log x + log y))       : by rw ←exp_add
             ... = log x + log y                   : by rw log_exp_eq

end ex6

namespace ex7
/-
Prove the theorem below, using only the ring properties of Z enumerated in
Section 4.2 and the theorem sub_self
-/

#check sub_self
example (x: ℤ) : x * 0 = 0 :=
calc x * 0 = x * (1 - 1)   : by rw ←sub_self
       ... = x * 1 - x * 1 : by rw mul_sub
       ... = 0             : by rw sub_self

example (x: ℤ) : x * 0 = 0 :=
by simp [sub_self, mul_sub]

end ex7

end ch4

namespace ch5

namespace scratch

example (p q : Prop) : p ∨ q → q ∨ p :=
begin
  intro h,
  cases h with hp hq,
  right, exact hp,
  left, exact hq
end

example (p q : Prop) : p ∧ q → q ∧ p :=
begin
  intro h,
  cases h with hp hq,
  constructor, exact hq, exact hp
end

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
  intro h,
    cases h with hp hqr,
    cases hqr with hq hr,
      left, constructor, repeat { assumption },
      right, constructor, repeat { assumption },
  intro h,
    cases h with hpq hpr,
      cases hpq with hp hq,
        constructor, exact hp, left, exact hq,
      cases hpr with hp hr,
        constructor, exact hp, right, exact hr
end

example (p q : ℕ → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x :=
begin
  intro h,
  cases h with x px,
  constructor, left, exact px
end

example (p q : ℕ → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x :=
begin
  intro h,
  cases h with x px,
  existsi x, left, exact px
end

example (p q: ℕ → Prop): (∃ x, p x ∧ q x) → ∃ x,q x ∧ p x :=
begin
  intro h,
  cases h with x hpq,
  cases hpq with hp hq,
  existsi x,
  split; assumption
end

universes u v

def swap_pair {α : Type u} {β : Type v} : α × β → β × α :=
begin
  intro p,
  cases p with ha hb,
  split ; assumption
end

#reduce swap_pair (1, 2)

def swap_sum {α : Type u} {β : Type v} : α ⊕ β → β ⊕ α :=
begin
  intro p,
  cases p with ha hb,
  right, exact ha,
  left, exact hb
end

open nat

example (P : ℕ → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : ℕ) :=
begin
  cases m with m', exact h₀, exact h₁ m'
end

example (p q : Prop) : p ∧ ¬ p → q :=
begin
  intro h,
  cases h,
  contradiction
end

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) :=
begin
  intro h,
  cases h with hp hqr,
  cases hqr with hq hr,
    left, exact ⟨hp, hq⟩,
    right, exact ⟨hp, hr⟩
end

end scratch

namespace ex1
/-
Go back to the exercises in Chapter 3 and Chapter 4 and redo as many as you can
now with tactic proofs, using also rw and simp as appropriate.
-/

namespace from_chapter_3

universe u
variables p q r s : Prop

def id {α : Type u} (a : α) : α := a

example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
begin
  apply iff.intro,
  intro h,
    cases h with hpq hr,
    cases hpq with hp hq,
    constructor, assumption,
    constructor; assumption,
  intro h,
    cases h with hp hqr,
    cases hqr with hq hr,
    repeat { constructor }; assumption
end

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
begin
  apply iff.intro,
  intro h,
    cases h with hpq hr,
    cases hpq with hp hq,
    left, exact hp,
    right, left, exact hq,
    right, right, exact hr,
  intro h,
    cases h with hp hqr,
    left, left, exact hp,
    cases hqr with hq hr,
    left, right, exact hq,
    right, exact hr
end

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
sorry

example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
sorry

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
sorry

example: (p → (q → r)) ↔ (p ∧ q → r) :=
sorry

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
sorry

example: ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
sorry

example: ¬p ∨ ¬q → ¬(p ∧ q) :=
sorry

example : ¬(p ∧ ¬p) := by simp

example: p ∧ ¬q → ¬(p → q) :=
sorry

example: ¬p → (p → q) :=
sorry

example: (¬p ∨ q) → (p → q) :=
sorry

example : p ∨ false ↔ p := by simp

example : p ∧ false ↔ false := by simp

example : (p → q) → (¬q → ¬p) :=
sorry

namespace with_classical
open classical

example : ¬(p ↔ ¬p) :=
sorry

example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
sorry

example : ¬(p ∧ q) → ¬p ∨ ¬q :=
sorry

example : ¬(p → q) → p ∧ ¬q :=
begin
  intro h,
  cases (em p) with hp np,
    constructor,
      exact hp,
      assume hq : q,
      have : p → q := λ _, hq,
      exact (h this),
    have : p → q, by { intro, contradiction },
      contradiction
end

example : (p → q) → (¬p ∨ q) :=
sorry

example : (¬q → ¬p) → (p → q) :=
sorry

example : p ∨ ¬p := em p

example : (((p → q) → p) → p) :=
sorry

end with_classical
end from_chapter_3
end ex1

namespace ex2
/-
Use tactic combinators to obtain a one line proof of the following:
-/
example (p q r : Prop) (hp : p) :
(p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
by simp [hp]

end ex2

end ch5

/- Chapter 6 -/
namespace ch6

namespace scratch

namespace x

universe u
variables {α : Type u} (r : α → α → Prop)

def reflexive : Prop := ∀ (a : α), r a a
def symmetric : Prop := ∀ {a b : α}, r a b → r b a
def transitive : Prop := ∀ {a b c : α}, r a b → r b c → r a c
def euclidean : Prop := ∀ {a b c : α}, r a b → r a c → r b c

variable {r}

theorem th1 (reflr : reflexive r) (euclr : euclidean r) :
  symmetric r :=
assume (a b : α),
assume : r a b,
show r b a, from euclr this (reflr _)

theorem th2 (symmr : symmetric r) (euclr : euclidean r) :
  transitive r :=
assume (a b c : α),
assume rab : r a b,
assume rbc : r b c,
show r a c, from euclr (symmr rab) rbc

theorem th3 (reflr : reflexive r) (euclr : euclidean r) :
  transitive r :=
@th2 _ _ (@th1 _ _ reflr @euclr) @euclr

end x

namespace y

universe u
variables {α : Type u} (r : α → α → Prop)

def reflexive : Prop := ∀ (a : α), r a a
def symmetric : Prop := ∀ ⦃ a b : α ⦄ , r a b → r b a
def transitive : Prop := ∀ ⦃ a b c : α ⦄, r a b → r b c → r a c
def euclidean : Prop := ∀ ⦃ a b c : α ⦄, r a b → r a c → r b c

variable {r}

theorem th1 (reflr : reflexive r) (euclr : euclidean r) :
  symmetric r :=
assume (a b : α),
assume : r a b,
show r b a, from euclr this (reflr _)

theorem th2 (symmr : symmetric r) (euclr : euclidean r) :
  transitive r :=
assume (a b c : α),
assume rab : r a b,
assume rbc : r b c,
show r a c, from euclr (symmr rab) rbc

theorem th3 (reflr : reflexive r) (euclr : euclidean r) :
  transitive r := th2 (th1 reflr euclr) euclr

end y

end scratch

end ch6