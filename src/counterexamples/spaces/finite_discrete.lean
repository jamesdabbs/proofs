/-
  Reading list:
  - https://leanprover.github.io/logic_and_proof/index.html
    - Especially https://leanprover.github.io/logic_and_proof/sets.html
-/
prelude
import topology.order topology.subset_properties
import data.set data.set.basic
import set_theory.zfc

open set
open topological_space

universes u
variables {α β: Type u} [topological_space α] {A B C : set α}

section discrete

def is_discrete (s : set α) : Prop :=
∀ t ⊆ s, is_open t

class discrete_space (α : Type u) [topological_space α] : Prop :=
(is_discrete_univ : is_discrete (univ : set α))

lemma comp_intersect : A ∩ (B \ A) = ∅ :=
begin
   apply set.eq_empty_of_subset_empty,
   assume x,
   assume h : x ∈ A ∩ (B \ A),
   have a : x ∈ A, from and.left h,
   have : x ∈ B \ A, from and.right h,
   have c : x ∉ A, from and.right this,
   show x ∈ ∅, from absurd a c
end

theorem is_totally_separated_of_is_discrete {s : set α}
  (H : is_discrete s) : is_totally_separated s :=
begin
  rewrite is_totally_separated,
  intros,
  fapply exists.intro,
  exact singleton(x),
  fapply exists.intro,
  exact (s \ {x}),
  split,
  -- {x} is open
  apply H,
  rewrite set.singleton_subset_iff,
  assumption,
  split,
  -- s \ {x} is open
  apply H,
  simp,
  split,
  -- x ∈ {x}
  simp,
  split,
  -- y ∈ s \ {x}
  simp,
  split,
  assumption,
  show ¬y = x,
    finish,
    split,
  show s ⊆ {x} ∪ s \ {x},
    intros,
    rewrite set.union_diff_cancel,
  show {x} ⊆ s,
    rw set.singleton_subset_iff,
    assumption,
  show {x} ∩ (s \ {x}) = ∅,
    exact comp_intersect
end

instance discrete_space.totally_separated_space (α : Type u) [topological_space α]
  [discrete_space α] : totally_separated_space α :=
⟨is_totally_separated_of_is_discrete $ discrete_space.is_discrete_univ _⟩

/-
  TODO:
  * is_totally_separated A -> |A| > 1 -> ¬ is_connected A
  * is_discrete -> is_compact
-/

end discrete

section indiscrete

def is_indiscrete (s : set α) : Prop :=
  is_open s -> s = ∅ ∨ s = univ

class indiscrete_space (α : Type u) [topological_space α] : Prop :=
(is_indiscrete_univ : is_indiscrete (univ : set α))

variable (s : set α)
#check is_indiscrete s

lemma nontrivial_nonempty [indiscrete_space α] (s : set α)
  (o : is_open s) (i : ∃ x, x ∈ s) : s = univ :=
begin
  cases i with x xs,
  have : s = ∅ ∨ s = univ, from sorry,
  cases this with empty full,
    have : x ∉ ∅, from set.not_mem_empty x,
    rewrite empty at xs,
    contradiction,
    assumption
end

instance indiscrete_space.irreducible_space (α : Type u) [topological_space α]
  [indiscrete_space α] : irreducible_space α := ⟨
    begin
      rewrite is_irreducible,
      assume u v : set α,
      assume ou : is_open u,
      assume ov : is_open v,
      assume : ∃ x, x ∈ univ ∩ u,
      cases this with x iu,
      have : x ∈ u, from iu.right,
      have au : u = univ, from nontrivial_nonempty u ou ⟨x, this⟩,
      rewrite au,
      assume : ∃ y, y ∈ univ ∩ v,
      cases this with y iv,
      have : y ∈ v, from iv.right,
      have av : v = univ, from nontrivial_nonempty v ov ⟨y, this⟩,
      rewrite av,
      exact ⟨x, by simp⟩
    end
  ⟩

theorem is_compact_of_is_indiscrete
  (H : is_indiscrete (univ : set α)) : compact (univ : set α) :=
begin
  rw compact_iff_finite_subcover,
  intros,
  suffices : ∃ x ∈ univ, sorry,
  cases this with x xu,
  have : x ∈ ⋃₀ c, from sorry,
  have : ∃ t ∈ c, x ∈ t, from sorry,
  cases this with t tu,
  have : t = univ, from sorry,
  exact ⟨singleton(t), sorry⟩
end

instance indiscrete_space.compact_space (α : Type u) [topological_space α]
  [indiscrete_space α] : compact_space α :=
⟨is_compact_of_is_indiscrete $ indiscrete_space.is_indiscrete_univ _⟩

end indiscrete