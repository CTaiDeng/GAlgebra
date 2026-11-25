import GAlgebra.Operators

set_option autoImplicit false
namespace GAlgebra

def jointKineticLimitGoal {Input Scale : Type _}
    (prepared : Input → Prop) (power cutoff : Scale → Prop)
    (jointConvergence : Input → Scale → Scale → Prop) : Prop :=
  ∀ input, prepared input → ∃ β radius, power β ∧ cutoff radius ∧ jointConvergence input β radius

def globalClassicalEvolutionGoal {Input Solution : Type _}
    (legal : Input → Prop) (solvesGlobally : Input → Solution → Prop) : Prop :=
  ∀ input, legal input → ∃ solution, solvesGlobally input solution

def uniqueGlobalClassicalEvolutionGoal {Input Solution : Type _}
    (legal : Input → Prop) (solvesGlobally : Input → Solution → Prop) : Prop :=
  ∀ input, legal input → ∃ solution, solvesGlobally input solution ∧
    ∀ other, solvesGlobally input other → other = solution

def kineticTotalDifferential {A E C : Type _} [Abelian A] [Abelian E] [Abelian C]
    (dA : AddMap A A) (dE : AddMap E E) (dC : AddMap C C)
    (first : AddMap A E) (second : AddMap E C) (homotopy : AddMap A C)
    (point : A × E × C) : A × E × C :=
  let (x, y, z) := point
  (dA x, first x + -dE y, dC z + second y + -homotopy x)

theorem kinetic_total_square_identity {A E C : Type _} [Abelian A] [Abelian E] [Abelian C]
    (dA : AddMap A A) (dE : AddMap E E) (dC : AddMap C C)
    (first : AddMap A E) (second : AddMap E C) (homotopy : AddMap A C)
    (squareA : ∀ x, dA (dA x) = 0) (squareE : ∀ y, dE (dE y) = 0)
    (squareC : ∀ z, dC (dC z) = 0)
    (firstChain : ∀ x, first (dA x) = dE (first x))
    (secondChain : ∀ y, dC (second y) = second (dE y))
    (x : A) (y : E) (z : C) :
    let D := kineticTotalDifferential dA dE dC first second homotopy
    D (D (x, y, z)) = (0, 0, second (first x) + -(dC (homotopy x) + homotopy (dA x))) := by
  dsimp only [kineticTotalDifferential]
  simp only [squareA, dE.map_add, dE.map_neg, dC.map_add, dC.map_neg,
    second.map_add, second.map_neg, squareE, squareC, firstChain, secondChain,
    Abelian.neg_zero, Abelian.add_zero, Abelian.zero_add, Abelian.add_neg]
  congr 2
  rw [Abelian.neg_add_rev]
  calc
    _ = (second (first x) + (-homotopy (dA x) + -dC (homotopy x))) +
          (second (dE y) + -second (dE y)) := by ac_rfl
    _ = _ := by rw [Abelian.add_neg, Abelian.add_zero]

theorem kinetic_total_closure_iff {A E C : Type _} [Abelian A] [Abelian E] [Abelian C]
    (dA : AddMap A A) (dE : AddMap E E) (dC : AddMap C C)
    (first : AddMap A E) (second : AddMap E C) (homotopy : AddMap A C)
    (squareA : ∀ x, dA (dA x) = 0) (squareE : ∀ y, dE (dE y) = 0)
    (squareC : ∀ z, dC (dC z) = 0)
    (firstChain : ∀ x, first (dA x) = dE (first x))
    (secondChain : ∀ y, dC (second y) = second (dE y)) :
    (∀ point,
      let D := kineticTotalDifferential dA dE dC first second homotopy
      D (D point) = (0, 0, 0)) ↔
      ∀ x, second (first x) = dC (homotopy x) + homotopy (dA x) := by
  have readback := kinetic_total_square_identity dA dE dC first second homotopy
    squareA squareE squareC firstChain secondChain
  constructor
  · intro closed x
    have check := (readback x 0 0).symm.trans (closed (x, 0, 0))
    exact Abelian.eq_of_difference_zero (congrArg (fun triple : A × E × C => triple.2.2) check)
  · rintro compare ⟨x, y, z⟩
    exact (readback x y z).trans (by rw [compare x, Abelian.add_neg])

theorem kinetic_occupancy_pair_bound (n : Int) (nonnegative : 0 ≤ n) :
    2 * n - n * (n - 1) ≤ 2 * (if 0 < n then 1 else 0) := by
  by_cases occupied : 0 < n
  · rw [ite_eq_left occupied]
    by_cases one : n = 1
    · subst n
      decide
    · have product := Int.mul_nonneg (show 0 ≤ n - 1 by omega) (show 0 ≤ n - 2 by omega)
      grind
  · have zero : n = 0 := by omega
    subst n
    decide

theorem kinetic_elastic_pair_balance (v w vNormal wNormal direction vEnergy wEnergy : Rat) :
    let impact := vNormal - wNormal
    (v - impact * direction) + (w + impact * direction) = v + w ∧
      (vEnergy - 2 * impact * vNormal + impact ^ 2) +
        (wEnergy + 2 * impact * wNormal + impact ^ 2) = vEnergy + wEnergy := by
  dsimp only
  simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
  constructor <;> grind

theorem kinetic_equilibrium_mass_budget (insertion retained : Rat)
    (insertionRange : 0 ≤ insertion ∧ insertion ≤ 1)
    (retainedRange : 0 ≤ retained ∧ retained ≤ 1) :
    0 ≤ 1 - insertion * retained ∧
      1 - insertion * retained ≤ (1 - insertion) + (1 - retained) := by
  have productBound := Rat.mul_le_mul_of_nonneg_left retainedRange.2 insertionRange.1
  simp only [Rat.mul_one] at productBound
  have remainder : 0 ≤ (1 - insertion) * (1 - retained) :=
    Rat.mul_nonneg (by grind) (by grind)
  constructor <;> grind

theorem kinetic_boussinesq_energy_readback (density temperature : Rat)
    (boussinesq : density + temperature = 0) :
    (3 - 5 : Rat) / 2 * density + (15 - 8 * 3 + 15 : Rat) / 4 * temperature =
      5 / 2 * temperature := by
  grind

theorem kinetic_scaled_error_budget (δ total particle kinetic tail particleBudget : Rat)
    (positive : 0 < δ)
    (estimate : total ≤ particle / δ + kinetic + tail)
    (particleBound : particle ≤ δ * particleBudget) :
    total ≤ particleBudget + kinetic + tail := by
  have scaled : particle / δ ≤ particleBudget := by
    apply Rat.le_of_mul_le_mul_right _ positive
    rw [Rat.div_mul_cancel (Rat.ne_of_gt positive), Rat.mul_comm particleBudget δ]
    exact particleBound
  grind

theorem kinetic_entropy_law_readback {Law Time : Type _}
    (transport : Time → Law → Law) (entropy count : Law → Rat) (result : Law → Prop)
    (initial : Law) (entropyBudget countBudget : Rat)
    (prepared : entropy initial ≤ entropyBudget ∧ count initial ≤ countBudget)
    (preserved : ∀ time law,
      entropy (transport time law) = entropy law ∧ count (transport time law) = count law)
    (readback : ∀ law, entropy law ≤ entropyBudget → count law ≤ countBudget → result law) :
    ∀ time, entropy (transport time initial) ≤ entropyBudget ∧
      count (transport time initial) ≤ countBudget ∧ result (transport time initial) := by
  intro time
  obtain ⟨sameEntropy, sameCount⟩ := preserved time initial
  have legalEntropy := sameEntropy.symm ▸ prepared.1
  have legalCount := sameCount.symm ▸ prepared.2
  exact ⟨legalEntropy, legalCount, readback _ legalEntropy legalCount⟩

theorem kinetic_entropy_hellinger_bound (root rootLog : Rat)
    (rootNonnegative : 0 ≤ root)
    (rootEntropyNonnegative : 0 ≤ root * rootLog - root + 1) :
    (root - 1) ^ 2 ≤ root ^ 2 * (2 * rootLog) - root ^ 2 + 1 := by
  have remainder := Rat.mul_nonneg (show 0 ≤ 2 * root by grind) rootEntropyNonnegative
  simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
  grind

theorem kinetic_centered_moment_budget
    (δ radius particle kinetic mass momentum centered cutoff total : Rat)
    (positive : 0 < δ)
    (massBound : mass ≤ particle + kinetic)
    (momentumBound : momentum ≤ radius * (particle + kinetic))
    (estimate : total ≤ (mass + momentum) / δ + centered + cutoff) :
    total ≤ (1 + radius) * (particle + kinetic) / δ + centered + cutoff := by
  have numerator : mass + momentum ≤ (1 + radius) * (particle + kinetic) := by grind
  have denominator : δ * ((1 + radius) * (particle + kinetic) / δ) =
      (1 + radius) * (particle + kinetic) := by
    rw [Rat.mul_comm δ, Rat.div_mul_cancel (Rat.ne_of_gt positive)]
  have scaledNumerator : mass + momentum ≤ δ * ((1 + radius) * (particle + kinetic) / δ) := by
    rw [denominator]
    exact numerator
  exact kinetic_scaled_error_budget δ total (mass + momentum) centered cutoff
    ((1 + radius) * (particle + kinetic) / δ) positive estimate scaledNumerator

theorem kinetic_power_gate (β exponent cutoff timeLoss : Rat) (positiveLoss : 0 < 1 + timeLoss) :
    0 < exponent - cutoff - (1 + timeLoss) * β ↔ β < (exponent - cutoff) / (1 + timeLoss) := by
  rw [Rat.lt_div_iff positiveLoss]
  grind

theorem kinetic_force_scale_readback (δ force density : Rat) (nonzero : δ ≠ 0) :
    (δ ^ 2 * force * density) / δ ^ 2 = force * density := by
  have squared : δ ^ 2 ≠ 0 := by
    simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
    intro zero
    exact (Rat.mul_eq_zero.mp zero).elim nonzero nonzero
  have factors : δ ^ 2 * force * density = (force * density) * δ ^ 2 := by grind
  rw [factors, Rat.mul_div_cancel squared]

theorem lattice_triad_conjugate_cancel (leftReal leftImag rightReal rightImag : Rat) :
    -(leftReal * rightImag + leftImag * rightReal) +
      -(leftReal * -rightImag + -leftImag * rightReal) = 0 := by
  grind

theorem lattice_center_relative_energy (p q : Int) :
    (p + q) ^ 2 + (p - q) ^ 2 = 2 * (p ^ 2 + q ^ 2) := by
  grind

theorem lattice_parity_reconstruct (center relative : Int) (sameParity : relative % 2 = center % 2) :
    (center + relative) / 2 + (center - relative) / 2 = center ∧
      (center + relative) / 2 - (center - relative) / 2 = relative := by
  omega

private theorem square_mod_four (x : Int) : x ^ 2 % 4 = x % 2 := by
  let quotient := x / 2
  by_cases even : x % 2 = 0
  · have split : x = 2 * quotient := by dsimp [quotient]; omega
    have square : x ^ 2 = 4 * (quotient * quotient) := by grind
    rw [square, even]
    omega
  · have odd : x % 2 = 1 := by omega
    have split : x = 2 * quotient + 1 := by dsimp [quotient]; omega
    have square : x ^ 2 = 4 * (quotient * quotient + quotient) + 1 := by grind
    rw [square, odd]
    omega

theorem lattice_divisible_collision_shell (x y z : Int)
    (multiple : (x ^ 2 + y ^ 2 + z ^ 2) % 4 = 0) :
    x % 2 = 0 ∧ y % 2 = 0 ∧ z % 2 = 0 := by
  have xResidue := square_mod_four x
  have yResidue := square_mod_four y
  have zResidue := square_mod_four z
  omega

end GAlgebra
