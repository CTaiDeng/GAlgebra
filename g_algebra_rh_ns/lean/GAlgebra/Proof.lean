import GAlgebra.Core

set_option autoImplicit false
namespace GAlgebra

inductive Derivation {P : Type _} (hyp : P → Prop) (rule : List P → P → Prop) : P → Prop
  | leaf {p : P} : hyp p → Derivation hyp rule p
  | apply {p : P} {xs : List P} :
      rule xs p → (∀ q, q ∈ xs → Derivation hyp rule q) → Derivation hyp rule p

theorem derivation_sound {P : Type _} {H V : P → Prop} {R : List P → P → Prop}
    (leaf : ∀ p, H p → V p) (node : ∀ xs p, R xs p → (∀ q, q ∈ xs → V q) → V p)
    {p : P} (h : Derivation H R p) : V p := by
  induction h with
  | leaf hp => exact leaf _ hp
  | apply hr _ ih => exact node _ _ hr ih

theorem translate_proof {P Q : Type _} {H : P → Prop} {H' : Q → Prop}
    {R : List P → P → Prop} {R' : List Q → Q → Prop} (read : P → Q)
    (leaf : ∀ p, H p → Derivation H' R' (read p))
    (node : ∀ xs p, R xs p → (∀ q, q ∈ xs → Derivation H' R' (read q)) →
      Derivation H' R' (read p))
    {p : P} (h : Derivation H R p) : Derivation H' R' (read p) :=
  derivation_sound leaf node h

theorem finite_dag_sound {N : Type _} (rank : N → Nat) (edge : N → N → Prop)
    (P : N → Prop) (low : ∀ c p, edge c p → rank c < rank p)
    (rule : ∀ p, (∀ c, edge c p → P c) → P p) : ∀ p, P p := by
  intro p
  have validAtRank : ∀ k : Nat, ∀ v, rank v = k → P v := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro v hv
      apply rule
      intro c hc
      exact ih (rank c) (hv ▸ low c v hc) c rfl
  exact validAtRank (rank p) p rfl

theorem discharge_open_hypotheses {P : Type _} {base fresh : P → Prop}
    {R : List P → P → Prop} (filled : ∀ p, fresh p → Derivation base R p)
    {p : P} (d : Derivation (fun q => base q ∨ fresh q) R p) : Derivation base R p := by
  apply translate_proof id ?_ ?_ d
  · intro q h
    exact h.elim Derivation.leaf (filled q)
  · intro _ _ hr hs
    exact Derivation.apply hr hs

theorem finite_branch_transport {m : Nat} (P Q : Fin m → Prop)
    (proofs : ∀ i, Q i) (replay : ∀ i, Q i → P i) : ∀ i, P i :=
  fun i => replay i (proofs i)

theorem gate_reflects_only_its_test (P Q : Prop) (reflect : Q ↔ P) :
    Q → P := reflect.mp

inductive Term (F : Type _) (arity : F → Nat)
  | var : Nat → Term F arity
  | app (f : F) : (Fin (arity f) → Term F arity) → Term F arity

namespace Term

def eval {X F : Type _} {arity : F → Nat}
    (ops : ∀ f, (Fin (arity f) → X) → X) (env : Nat → X) : Term F arity → X
  | .var n => env n
  | .app f args => ops f (fun i => eval ops env (args i))

theorem evaluations_commute {X Y F : Type _} {arity : F → Nat} (e : X → Y)
    (ops : ∀ f, (Fin (arity f) → X) → X) (ops' : ∀ f, (Fin (arity f) → Y) → Y)
    (h : ∀ f args, e (ops f args) = ops' f (fun i => e (args i)))
    (env : Nat → X) (t : Term F arity) :
    e (eval ops env t) = eval ops' (e ∘ env) t := by
  induction t with
  | var _ => rfl
  | app f args ih =>
    simp only [eval, h, ih]

end Term

theorem frozen_domain_cannot_be_widened :
    ∃ (R : Bool → Prop), (∀ _ : Unit, R true) ∧ ¬ (∀ b : Bool, R b) := by
  refine ⟨fun b => b = true, fun _ => rfl, ?_⟩
  exact fun h => Bool.noConfusion (h false)

inductive Formula (A : Type _)
  | atom : A → Formula A
  | bot : Formula A
  | conj : Formula A → Formula A → Formula A
  | impl : Formula A → Formula A → Formula A
  | all : Formula A → Formula A
  | ex : Formula A → Formula A

namespace Formula

def extend {X : Type _} (x : X) (env : Nat → X) : Nat → X
  | 0 => x
  | n + 1 => env n

def holds {X A : Type _} (I : A → (Nat → X) → Prop) (env : Nat → X) : Formula A → Prop
  | .atom a => I a env
  | .bot => False
  | .conj p q => holds I env p ∧ holds I env q
  | .impl p q => holds I env p → holds I env q
  | .all p => ∀ x, holds I (extend x env) p
  | .ex p => ∃ x, holds I (extend x env) p

theorem extend_map {X Y : Type _} (e : X → Y) (x : X) (env : Nat → X) :
    (e ∘ extend x env) = extend (e x) (e ∘ env) := by
  funext n
  cases n <;> rfl

theorem formula_transport {X Y A : Type _} (e : X → Y) (onto : ∀ y, ∃ x, e x = y)
    (I : A → (Nat → X) → Prop) (J : A → (Nat → Y) → Prop)
    (atoms : ∀ a env, I a env ↔ J a (e ∘ env))
    (p : Formula A) (env : Nat → X) :
    holds I env p ↔ holds J (e ∘ env) p := by
  induction p generalizing env with
  | atom a => exact atoms a env
  | bot => rfl
  | conj p q hp hq => exact and_congr (hp env) (hq env)
  | impl p q hp hq =>
    exact ⟨fun h a => (hq env).mp (h ((hp env).mpr a)),
      fun h a => (hq env).mpr (h ((hp env).mp a))⟩
  | all p ih =>
    constructor
    · intro h y
      obtain ⟨x, rfl⟩ := onto y
      have h' := (ih (extend x env)).mp (h x)
      rwa [extend_map] at h'
    · intro h x
      apply (ih (extend x env)).mpr
      rw [extend_map]
      exact h (e x)
  | ex p ih =>
    constructor
    · rintro ⟨x, h⟩
      refine ⟨e x, ?_⟩
      have h' := (ih (extend x env)).mp h
      rwa [extend_map] at h'
    · rintro ⟨y, h⟩
      obtain ⟨x, rfl⟩ := onto y
      refine ⟨x, (ih (extend x env)).mpr ?_⟩
      rwa [extend_map]

end Formula

end GAlgebra
