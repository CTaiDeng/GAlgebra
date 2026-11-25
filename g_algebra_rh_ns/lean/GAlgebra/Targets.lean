import GAlgebra.Operators

set_option autoImplicit false
namespace GAlgebra

/-- The signature required by the zero-line argument, with its analytic inputs explicit. -/
structure ZeroLineSpec (Z K : Type _) where
  nontrivial : Z → Prop
  realPart : Z → K
  half : K

def ZeroLineSpec.goal {Z K : Type _} (S : ZeroLineSpec Z K) : Prop :=
  ∀ z, S.nontrivial z → S.realPart z = S.half

theorem symmetric_half_line_reduction {Z K : Type _} [LE K]
    (S : ZeroLineSpec Z K) (mirror : Z → Z)
    (admissible : ∀ z, S.nontrivial z → S.nontrivial (mirror z))
    (reflects_le : ∀ z, S.realPart (mirror z) ≤ S.half → S.half ≤ S.realPart z)
    (antisymm : ∀ a b : K, a ≤ b → b ≤ a → a = b)
    (upper : ∀ z, S.nontrivial z → S.realPart z ≤ S.half) :
    S.goal := by
  intro z hz
  exact antisymm _ _ (upper z hz) (reflects_le z (upper (mirror z) (admissible z hz)))

/-- The classical forced-flow conclusion with compactness imposed on the force. -/
structure FlowSpec (Viscosity Force Velocity Pressure : Type _) where
  positive : Viscosity → Prop
  smoothCompact : Force → Prop
  interiorSmooth : Velocity → Pressure → Prop
  equation : Viscosity → Force → Velocity → Pressure → Prop
  divergenceFree : Velocity → Prop
  zeroInitial : Velocity → Prop
  energyBound : Velocity → Prop
  blowsUp : Velocity → Prop

def FlowSpec.atViscosity {N F U P : Type _} (S : FlowSpec N F U P) (ν : N) : Prop :=
  ∃ f u p, S.smoothCompact f ∧ S.interiorSmooth u p ∧
    S.equation ν f u p ∧ S.divergenceFree u ∧ S.zeroInitial u ∧
    S.energyBound u ∧ S.blowsUp u

def FlowSpec.goal {N F U P : Type _} (S : FlowSpec N F U P) : Prop :=
  ∀ ν, S.positive ν → S.atViscosity ν

theorem flow_mother_readback {Mother N F U P : Type _} (S : FlowSpec N F U P)
    (legal periodic nonzero : Mother → Prop)
    (read : ∀ x, legal x → periodic x → nonzero x → ∀ ν, S.positive ν → S.atViscosity ν) :
    (∃ x, legal x ∧ periodic x ∧ nonzero x) → S.goal := by
  intro closed
  obtain ⟨x, legalInput, exactPeriod, nonzeroProfile⟩ := closed
  intro ν hν
  exact read x legalInput exactPeriod nonzeroProfile ν hν

theorem finite_lattice_hit_iff {State : Type _} (lattice : List State) (check : State → Bool) :
    (lattice.find? check).isSome ↔ ∃ s, s ∈ lattice ∧ check s = true :=
  List.find?_isSome

theorem finite_lattice_hit_readback {State Target : Type _}
    (lattice : List State) (check : State → Bool) (read : State → Target)
    (valid : Target → Prop) (certificate : ∀ s, s ∈ lattice → check s = true → valid (read s))
    {s : State} (hit : lattice.find? check = some s) : valid (read s) :=
  certificate s (List.mem_of_find?_eq_some hit) (List.find?_some hit)


end GAlgebra
