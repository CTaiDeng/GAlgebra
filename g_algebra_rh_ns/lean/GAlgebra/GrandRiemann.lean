import GAlgebra.FiniteGeometry
import GAlgebra.Targets

set_option autoImplicit false
namespace GAlgebra

universe u v w

def grandRiemannGoal {Rep : Nat → Type u} {Z : (n : Nat) → Rep n → Type v} {K : Type w}
    (firstRank : Nat)
    (fibers : (n : Nat) → (π : Rep n) → ZeroLineSpec (Z n π) K) : Prop :=
  ∀ (n : Nat) (π : Rep (n + firstRank)), (fibers (n + firstRank) π).goal

theorem grand_riemann_fiber_equivalence {Rep : Nat → Type u}
    {Z : (n : Nat) → Rep n → Type v} {K : Type w}
    (firstRank : Nat)
    (fibers : (n : Nat) → (π : Rep n) → ZeroLineSpec (Z n π) K)
    (certificate : (n : Nat) → Rep n → Prop)
    (localReadback : ∀ (n : Nat) (π : Rep (n + firstRank)),
      certificate (n + firstRank) π ↔ (fibers (n + firstRank) π).goal) :
    grandRiemannGoal firstRank fibers ↔
      ∀ (n : Nat) (π : Rep (n + firstRank)), certificate (n + firstRank) π := by
  constructor
  · intro read n π
    exact (localReadback n π).mpr (read n π)
  · intro valid n π
    exact (localReadback n π).mp (valid n π)

theorem grand_riemann_rank_split {Rep : Nat → Type u}
    {Z : (n : Nat) → Rep n → Type v} {K : Type w}
    (fibers : (n : Nat) → (π : Rep n) → ZeroLineSpec (Z n π) K) :
    grandRiemannGoal 1 fibers ↔
      ((∀ π : Rep 1, (fibers 1 π).goal) ∧ grandRiemannGoal 2 fibers) := by
  constructor
  · intro full
    exact ⟨full 0, fun n π => full (n + 1) π⟩
  · rintro ⟨rankOne, higher⟩ n
    cases n with
    | zero => exact rankOne
    | succ n => exact higher n

theorem grand_riemann_rank_one_readback {Rep : Nat → Type u}
    {Z : (n : Nat) → Rep n → Type v} {K : Type w}
    (fibers : (n : Nat) → (π : Rep n) → ZeroLineSpec (Z n π) K)
    (zeta : Rep 1) (full : grandRiemannGoal 1 fibers) : (fibers 1 zeta).goal :=
  full 0 zeta

theorem zero_line_readback_along_shift {Z W K : Type _}
    (base : ZeroLineSpec Z K) (twist : ZeroLineSpec W K) (shift : W → Z)
    (zeroTransport : ∀ z, twist.nontrivial z → base.nontrivial (shift z))
    (realPartPreserved : ∀ z, base.realPart (shift z) = twist.realPart z)
    (sameLine : base.half = twist.half) (baseProof : base.goal) : twist.goal := by
  intro z hz
  rw [← realPartPreserved z, ← sameLine]
  exact baseProof (shift z) (zeroTransport z hz)

open Lean.Grind in
theorem dirichlet_gauss_rescale_vanish {K : Type _} [Field K]
    (character value : K) (nontrivial : character ≠ 1) (rescale : character * value = value) :
    value = 0 := by
  have product : (character - 1) * value = 0 := by grind
  have notZero : character - 1 ≠ 0 := by grind
  exact (Field.of_mul_eq_zero product).resolve_left notZero

def automorphicSquareSpectrum (real imag : Rat) : Rat × Rat :=
  (9 / 4 - (real - 1 / 2) ^ 2 + imag ^ 2, -2 * ((real - 1 / 2) * imag))

private theorem rat_square_nonnegative (x : Rat) : 0 ≤ x * x := by
  rcases Rat.le_total (a := 0) (b := x) with nonnegative | nonpositive
  · exact Rat.mul_nonneg nonnegative nonnegative
  · have opposite : 0 ≤ -x := by grind
    calc
      0 ≤ (-x) * (-x) := Rat.mul_nonneg opposite opposite
      _ = x * x := by grind

theorem automorphic_square_halfline (real imag : Rat) :
    (automorphicSquareSpectrum real imag).2 = 0 ∧
      9 / 4 ≤ (automorphicSquareSpectrum real imag).1 ↔ real = 1 / 2 := by
  simp only [automorphicSquareSpectrum, Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
  constructor
  · rintro ⟨imaginaryZero, onHalfline⟩
    have product : (real - 1 / 2) * imag = 0 :=
      (Rat.mul_eq_zero.mp imaginaryZero).resolve_left (by decide)
    rcases Rat.mul_eq_zero.mp product with centered | realZero
    · grind
    · rw [realZero] at onHalfline
      have square : (real - 1 / 2) * (real - 1 / 2) ≤ 0 := by grind
      have zero := Rat.le_antisymm square (rat_square_nonnegative (real - 1 / 2))
      have centered := (Rat.mul_eq_zero.mp zero).elim id id
      grind
  · intro centered
    subst real
    have square := rat_square_nonnegative imag
    exact ⟨by grind, by grind⟩

theorem automorphic_kernel_difference (a pole x y : Rat) :
    (x - a) * (pole - y) - (y - a) * (pole - x) = (x - y) * (pole - a) := by
  grind

theorem automorphic_real_weight_sign (boundary pole multiplicity : Rat)
    (positive : 0 < multiplicity) :
    0 ≤ multiplicity * (pole - boundary) ↔ boundary ≤ pole := by
  constructor
  · intro nonnegative
    have scaled : 0 * multiplicity ≤ (pole - boundary) * multiplicity := by
      simpa only [Rat.zero_mul, Rat.mul_comm (pole - boundary)] using nonnegative
    have difference := Rat.le_of_mul_le_mul_right scaled positive
    grind
  · intro onHalfline
    exact Rat.mul_nonneg (Rat.le_of_lt positive) (by grind)

theorem finite_diagonal_form_nonnegative_iff {Mode : Type _} [DecidableEq Mode]
    (modes : List Mode) (distinct : modes.Nodup) (weight : Mode → Rat) :
    (∀ v : Mode → Rat, 0 ≤ finiteSum (fun i => weight i * v i ^ 2) modes) ↔
      ∀ i ∈ modes, 0 ≤ weight i := by
  constructor
  · intro nonnegative i member
    let v : Mode → Rat := fun j => if j = i then 1 else 0
    have isolated := finiteSum_single_of_nodup (fun j => weight j * v j ^ 2)
      distinct member (fun j _ other => by simp [v, other, Rat.pow_succ, Rat.mul_zero])
    have bound := nonnegative v
    rw [isolated] at bound
    simpa [v, Rat.pow_succ, Rat.one_mul, Rat.mul_one] using bound
  · intro weights v
    have bound := contour_finite_upper_bound modes (fun _ => (0 : Rat))
      (fun i => weight i * v i ^ 2) fun i member =>
        Rat.mul_nonneg (weights i member)
          (by simpa only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
            using rat_square_nonnegative (v i))
    simpa only [finiteSum_zero_of_members modes (fun _ _ => rfl)] using bound

theorem automorphic_defect_zero_iff (imaginaryDefect positionDefect : Rat)
    (imaginaryNonnegative : 0 ≤ imaginaryDefect) (positionNonnegative : 0 ≤ positionDefect) :
    imaginaryDefect + positionDefect = 0 ↔ imaginaryDefect = 0 ∧ positionDefect = 0 := by
  constructor <;> intro h <;> grind

theorem automorphic_dyadic_tail_constant : (2 * 3 : Rat) / (1 - 1 / 16) = 32 / 5 := by
  decide +kernel

open Lean.Grind Std in
/-- The two moment inequalities are invariant under the trivial fiber's factor of two. -/
theorem grh_trivial_moment_scale {K : Type w} [CommRing K] [LE K] [LT K]
    [IsLinearOrder K] [LawfulOrderLT K] [OrderedRing K] (shifted mass cap : K) :
    (0 ≤ 2 * shifted ∧ 2 * shifted ≤ cap * (2 * mass)) ↔
      (0 ≤ shifted ∧ shifted ≤ cap * mass) := by
  grind

open Lean.Grind Std in
/-- Restrict the given family of moment witnesses to rank one, normalize, and read back once. -/
theorem grh_trivial_moment_readback {Rep : Nat → Type u} {Test : Type v} {K : Type w}
    {Z : Type _} [CommRing K] [LE K] [LT K] [IsLinearOrder K] [LawfulOrderLT K] [OrderedRing K]
    (zeta : ZeroLineSpec Z K) (trivialFiber : Rep 1) (cap : K)
    (shifted mass : (n : Nat) → Rep n → Test → K) (zetaShifted zetaMass : Test → K)
    (trivialShifted : ∀ p, shifted 1 trivialFiber p = 2 * zetaShifted p)
    (trivialMass : ∀ p, mass 1 trivialFiber p = 2 * zetaMass p)
    (familyWitness : ∀ (k : Nat) (π : Rep (k + 1)) (p : Test),
      0 ≤ shifted (k + 1) π p ∧ shifted (k + 1) π p ≤ cap * mass (k + 1) π p)
    (readback : (∀ p, 0 ≤ zetaShifted p ∧ zetaShifted p ≤ cap * zetaMass p) → zeta.goal) :
    zeta.goal := by
  apply readback
  intro p
  have bounds := familyWitness 0 trivialFiber p
  rw [trivialShifted p, trivialMass p] at bounds
  exact (grh_trivial_moment_scale (zetaShifted p) (zetaMass p) cap).mp bounds

end GAlgebra
