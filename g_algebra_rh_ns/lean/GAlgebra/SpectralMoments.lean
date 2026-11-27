import Init

set_option autoImplicit false
namespace GAlgebra

section Resolvent

open Lean.Grind

def poleDenominator {K : Type _} [Field K] (poles : List K) (point : K) : K :=
  (poles.map (fun pole => point - pole)).prod

def poleNumerator {K : Type _} [Field K] (residue : K → K) : List K → K → K
  | [], _ => 0
  | pole :: rest, point =>
    residue pole * poleDenominator rest point +
      (point - pole) * poleNumerator residue rest point

theorem pole_denominator_eq_zero {K : Type _} [Field K]
    (poles : List K) (point : K) (inside : point ∈ poles) :
    poleDenominator poles point = 0 := by
  induction poles with
  | nil => simp at inside
  | cons pole rest ih =>
    change (point - pole) * poleDenominator rest point = 0
    rcases List.mem_cons.mp inside with equal | tail
    · simp [equal, AddCommGroup.sub_self, Semiring.zero_mul]
    · rw [ih tail, Semiring.mul_zero]

theorem pole_denominator_ne_zero {K : Type _} [Field K]
    (poles : List K) (point : K) (outside : point ∉ poles) :
    poleDenominator poles point ≠ 0 := by
  induction poles with
  | nil => exact Ne.symm Field.zero_ne_one
  | cons pole rest ih =>
    have not_head : point ≠ pole := fun equal => outside (List.mem_cons.mpr (Or.inl equal))
    have not_tail : point ∉ rest := fun tail => outside (List.mem_cons.mpr (Or.inr tail))
    have head_nonzero : point - pole ≠ 0 := by grind
    intro zero
    change (point - pole) * poleDenominator rest point = 0 at zero
    exact (Field.of_mul_eq_zero zero).elim head_nonzero (ih not_tail)

theorem finite_resolvent_common_denominator {K : Type _} [Field K]
    (residue : K → K) (poles : List K) (point : K) (outside : point ∉ poles) :
    poleDenominator poles point *
      (poles.map (fun pole => residue pole / (point - pole))).sum =
        poleNumerator residue poles point := by
  induction poles with
  | nil => simp [poleDenominator, poleNumerator, Semiring.mul_zero]
  | cons pole rest ih =>
    have not_head : point ≠ pole := fun equal => outside (List.mem_cons.mpr (Or.inl equal))
    have not_tail : point ∉ rest := fun tail => outside (List.mem_cons.mpr (Or.inr tail))
    have head_nonzero : point - pole ≠ 0 := by grind
    have cancel : (point - pole) * (residue pole / (point - pole)) = residue pole := by
      rw [Field.div_eq_mul_inv]
      have inverse := Field.mul_inv_cancel head_nonzero
      calc
        _ = residue pole * ((point - pole) * (point - pole)⁻¹) := by grind
        _ = _ := by rw [inverse, Semiring.mul_one]
    change
      ((point - pole) * poleDenominator rest point) *
        (residue pole / (point - pole) +
          (rest.map (fun p => residue p / (point - p))).sum) = _
    calc
      _ = poleDenominator rest point * ((point - pole) * (residue pole / (point - pole))) +
          (point - pole) * (poleDenominator rest point *
            (rest.map (fun p => residue p / (point - p))).sum) := by grind
      _ = _ := by
        rw [cancel, ih not_tail]
        simp [poleNumerator, CommSemiring.mul_comm]

theorem finite_resolvent_numerator_ne_zero_at_pole {K : Type _} [Field K]
    (residue : K → K) (poles : List K) (point : K) (distinct : poles.Nodup)
    (inside : point ∈ poles) (nonzero_residue : residue point ≠ 0) :
    poleNumerator residue poles point ≠ 0 := by
  induction poles with
  | nil => simp at inside
  | cons pole rest ih =>
    obtain ⟨head_not_tail, tail_distinct⟩ := List.nodup_cons.mp distinct
    rcases List.mem_cons.mp inside with equal | tail
    · subst pole
      have rest_nonzero := pole_denominator_ne_zero rest point head_not_tail
      simp only [poleNumerator, AddCommGroup.sub_self, Semiring.zero_mul, AddCommMonoid.add_zero]
      intro zero
      exact (Field.of_mul_eq_zero zero).elim nonzero_residue rest_nonzero
    · have not_head : point ≠ pole := fun equal => head_not_tail (equal ▸ tail)
      have head_nonzero : point - pole ≠ 0 := by grind
      have tail_nonzero := ih tail_distinct tail
      simp only [poleNumerator, pole_denominator_eq_zero rest point tail,
        Semiring.mul_zero, AddCommMonoid.zero_add]
      intro zero
      exact (Field.of_mul_eq_zero zero).elim head_nonzero tail_nonzero

theorem xi_reflected_resolvent_split {K : Type _} [Field K] (s zero : K)
    (firstNonzero : s - zero ≠ 0) (secondNonzero : s - 1 + zero ≠ 0) :
    (s + s - 1) / ((s - zero) * (s - 1 + zero)) =
      1 / (s - zero) + 1 / (s - 1 + zero) := by
  let first := s - zero
  let second := s - 1 + zero
  have numerator : s + s - 1 = first + second := by
    dsimp [first, second]
    grind
  have firstCancel : first * first⁻¹ = 1 := Field.mul_inv_cancel firstNonzero
  have secondCancel : second * second⁻¹ = 1 := Field.mul_inv_cancel secondNonzero
  change (s + s - 1) / (first * second) = 1 / first + 1 / second
  rw [numerator]
  simp only [Field.div_eq_mul_inv, Field.inv_mul, Semiring.one_mul]
  calc
    _ = (second * second⁻¹) * first⁻¹ + (first * first⁻¹) * second⁻¹ := by grind
    _ = _ := by rw [firstCancel, secondCancel, Semiring.one_mul, Semiring.one_mul]

end Resolvent

theorem theta_small_height_bound (height remainder : Rat)
    (window : height ^ 2 ≤ 36) (nonnegative : 0 ≤ remainder)
    (small : remainder ≤ 10832 / 404595) :
    (1 + height ^ 2) * remainder < 1 := by
  have scaled := Rat.mul_le_mul_of_nonneg_right (show 1 + height ^ 2 ≤ 37 by grind) nonnegative
  grind

theorem spectral_localizing_forms (cap mass shifted : Rat) :
    (0 ≤ shifted ∧ shifted ≤ cap * mass) ↔
      (0 ≤ shifted ∧ 0 ≤ cap * mass - shifted) := by
  grind

theorem spectral_localizing_forms_all {Polynomial : Type _}
    (cap : Rat) (mass shifted : Polynomial → Rat) :
    (∀ p, 0 ≤ shifted p ∧ shifted p ≤ cap * mass p) ↔
      (∀ p, 0 ≤ shifted p ∧ 0 ≤ cap * mass p - shifted p) := by
  constructor
  · intro positive p
    exact (spectral_localizing_forms cap (mass p) (shifted p)).mp (positive p)
  · intro positive p
    exact (spectral_localizing_forms cap (mass p) (shifted p)).mpr (positive p)

section Bernstein

open Lean.Grind
attribute [local instance] Semiring.natCast
variable {K : Type _} [CommRing K]

def bernsteinFalling (x : K) : Nat → K
  | 0 => 1
  | r + 1 => (x - (r : K)) * bernsteinFalling x r

private theorem bernstein_falling_zero (r : Nat) :
    bernsteinFalling (0 : K) (r + 1) = 0 := by
  induction r with
  | zero =>
    change (0 - ((0 : Nat) : K)) * 1 = 0
    rw [Semiring.natCast_zero]
    grind
  | succ r ih => rw [bernsteinFalling, ih, Semiring.mul_zero]

private theorem bernstein_falling_shift (x : K) (r : Nat) :
    bernsteinFalling (x + 1) (r + 1) = (x + 1) * bernsteinFalling x r := by
  induction r with
  | zero =>
    change (x + 1 - ((0 : Nat) : K)) * 1 = (x + 1) * 1
    rw [Semiring.natCast_zero]
    grind
  | succ r ih =>
    change (x + 1 - ((r + 1 : Nat) : K)) * bernsteinFalling (x + 1) (r + 1) =
      (x + 1) * ((x - (r : K)) * bernsteinFalling x r)
    rw [ih, Semiring.natCast_succ]
    grind

private theorem bernstein_falling_difference (x : K) (r : Nat) :
    bernsteinFalling (x + 1) (r + 1) =
      bernsteinFalling x (r + 1) + ((r + 1 : Nat) : K) * bernsteinFalling x r := by
  rw [bernstein_falling_shift]
  change (x + 1) * bernsteinFalling x r =
    (x - (r : K)) * bernsteinFalling x r + ((r + 1 : Nat) : K) * bernsteinFalling x r
  rw [Semiring.natCast_succ]
  grind

def bernsteinAverage (x : K) : Nat → (Nat → K) → K
  | 0, f => f 0
  | n + 1, f =>
    (1 - x) * bernsteinAverage x n f + x * bernsteinAverage x n (fun k => f (k + 1))

private theorem bernstein_average_constant (x value : K) (n : Nat) :
    bernsteinAverage x n (fun _ => value) = value := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [bernsteinAverage, ih]
    grind

private theorem bernstein_average_linear (x a : K) (n : Nat) (f g : Nat → K) :
    bernsteinAverage x n (fun k => f k + a * g k) =
      bernsteinAverage x n f + a * bernsteinAverage x n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [bernsteinAverage, ih f g, ih (fun k => f (k + 1)) (fun k => g (k + 1))]
    grind

theorem bernstein_falling_average (x : K) (n r : Nat) :
    bernsteinAverage x n (fun k => bernsteinFalling (k : K) r) =
      bernsteinFalling (n : K) r * x ^ r := by
  induction n generalizing r with
  | zero =>
    cases r with
    | zero =>
      change (1 : K) = 1 * x ^ 0
      rw [Semiring.pow_zero, Semiring.mul_one]
    | succ r =>
      change bernsteinFalling ((0 : Nat) : K) (r + 1) =
        bernsteinFalling ((0 : Nat) : K) (r + 1) * x ^ (r + 1)
      rw [Semiring.natCast_zero, bernstein_falling_zero, Semiring.zero_mul]
  | succ n ih =>
    cases r with
    | zero =>
      simpa only [bernsteinFalling, Semiring.pow_zero, Semiring.mul_one] using
        bernstein_average_constant x (1 : K) (n + 1)
    | succ r =>
      have shifted :
          (fun k : Nat => bernsteinFalling ((k + 1 : Nat) : K) (r + 1)) =
            (fun k : Nat => bernsteinFalling (k : K) (r + 1) +
              ((r + 1 : Nat) : K) * bernsteinFalling (k : K) r) := by
        funext k
        rw [Semiring.natCast_succ, bernstein_falling_difference]
      simp only [bernsteinAverage]
      rw [shifted, bernstein_average_linear, ih (r + 1), ih r,
        Semiring.natCast_succ (α := K) n, bernstein_falling_difference, Semiring.pow_succ]
      grind

end Bernstein

theorem spectral_positive_quotient_bound (cap mass shifted : Rat)
    (capNonnegative : 0 ≤ cap) (massNonnegative : 0 ≤ mass)
    (shiftedNonnegative : 0 ≤ shifted)
    (squareBound : shifted * shifted ≤ (cap * mass) * shifted) :
    shifted ≤ cap * mass := by
  by_cases zero : shifted = 0
  · rw [zero]
    exact Rat.mul_nonneg capNonnegative massNonnegative
  · exact Rat.le_of_mul_le_mul_right squareBound (by grind)

theorem spectral_upper_weight_numerator (a inverseA pole inversePole multiplicity : Rat)
    (boundaryInverse : a * inverseA = 1) (poleInverse : pole * inversePole = 1) :
    a * (multiplicity * inversePole * (inverseA - inversePole)) =
      multiplicity * (pole - a) * (inversePole * inversePole) := by
  calc
    _ = multiplicity * inversePole * (a * inverseA - a * inversePole) := by grind
    _ = multiplicity * inversePole * (pole * inversePole - a * inversePole) := by
      rw [boundaryInverse, poleInverse]
    _ = _ := by grind

theorem xi_polynomial_sector_constants :
    1 / 38 + 1 / 38 < (4 / 9 : Rat) ∧
    6 / 19 + 2 * 76 * (3 / 722) = (18 / 19 : Rat) ∧
    (18 / 19 : Rat) ^ 2 < 1 := by
  decide +kernel

theorem xi_exterior_factor_constants :
    (305 : Rat) / 10 ^ 14 < 1 / (210 : Rat) ^ 5 + (313 / 338 : Rat) / 270 ^ 5 ∧
    (16 : Rat) ^ 2 + 5 / 2 < 270 ∧
    2 / 270 < (4 / 9 : Rat) ∧
    (1 / 210 - 1 / 270 : Rat) * 945 = 1 ∧
    (2835 : Rat) / (270 * 16) = 21 / 32 ∧
    2 * (21 / 32 + 76 / (270 * 16) : Rat) < 27 / 20 ∧
    1 - (27 / 20 : Rat) ^ 2 / 2 > 1 / 16 := by
  decide +kernel

theorem xi_exterior_factor_phase (angle weight roots budget : Rat)
    (angleRange : 0 ≤ angle ∧ angle ≤ budget)
    (weightRange : 0 ≤ weight ∧ weight ≤ angle)
    (rootsRange : 0 ≤ roots ∧ roots ≤ budget) :
    (-2 * budget ≤ 2 * angle - 2 * roots ∧ 2 * angle - 2 * roots ≤ 2 * budget) ∧
      (-2 * budget ≤ angle - weight - 2 * roots ∧ angle - weight - 2 * roots ≤ 2 * budget) := by
  grind

theorem xi_origin_summation_bounds :
    (1 + 16 / 2 + 120 / 6 + 1820 / 30 + 8008 / 42 + 12870 / 30 +
      8008 * 5 / 66 + 1820 * 691 / 2730 + 120 * 7 / 6 + 3617 / 510 : Rat) < 10000 ∧
    (10000 * 17 * 18 * 19 * 20 : Rat) / (24 * 16 * 64 ^ 16) < 1 / 10 ^ 22 := by
  decide +kernel

theorem xi_origin_moment_bounds (c0 c1 c2 c3 c4 : Rat)
    (bounds0 : 6906623153000067 / 100000000000000000 ≤ c0 ∧
      c0 ≤ 6906623153000068 / 100000000000000000)
    (bounds1 : 4571535067558049 / 100000000000000000 ≤ c1 ∧
      c1 ≤ 4571535067558050 / 100000000000000000)
    (bounds2 : -32502923154427 / 100000000000000000 ≤ c2 ∧
      c2 ≤ -32502923154426 / 100000000000000000)
    (bounds3 : -6808631547988 / 100000000000000000 ≤ c3 ∧
      c3 ≤ -6808631547987 / 100000000000000000)
    (bounds4 : 201194269826 / 100000000000000000 ≤ c4 ∧
      c4 ≤ 201194269827 / 100000000000000000) :
    let lowerMoment := 20 / 2187 * c0 - 10 / 729 * c1 + 4 / 243 * c2 - c3 / 81
    let upperMoment :=
      70 / 19683 * c0 - 35 / 6561 * c1 + 5 / 729 * c2 - 5 / 729 * c3 + c4 / 243
    0 < lowerMoment ∧ lowerMoment < 635 / 1000000000000 ∧
      304 / 100000000000000 < upperMoment ∧ upperMoment < 305 / 100000000000000 := by
  dsimp only
  grind

theorem xi_separated_pole_budgets :
    let momentUpper := (305 / 10 ^ 14 : Rat)
    let cosineLower := (313 / 338 : Rat)
    let cap := (4 / 9 : Rat)
    momentUpper < (497 / 722) / 180 ^ 5 ∧
    momentUpper < (2 * cosineLower) / 225 ^ 5 ∧
    momentUpper < 1 / 200 ^ 5 ∧
    (635 / 10 ^ 12 : Rat) < 210 * (304 / 10 ^ 14) ∧
    (momentUpper * 210 ^ 5 - 1) / cosineLower < 27 / 100 ∧
    (27 / 100 : Rat) * ((cap + 1 / 225) / (cap - 1 / 200)) < 7 / 25 ∧
    (27 / 100 : Rat) * (210 / 225) < 7 / 25 := by
  decide +kernel

theorem xi_shifted_coefficient_constants :
    let cap := (4 / 9 : Rat)
    let shiftRatio := (21 / 20000 : Rat)
    let perturbation := (13 / 500 : Rat)
    (6906623153000068 : Rat) / (3 * 10 ^ 17) < 3 / 125 ∧
    (99 / 100 : Rat) < 1 - (1 / 13) ^ 2 / 2 ∧
    (3 / 125 : Rat) / (99 / 100) < 1 / 40 ∧
    (44100 / 8000 : Rat) < 6 ∧
    (210 / 40 : Rat) * (cap + 1 / 200) / (cap - 1 / 200) < 6 ∧
    24 * shiftRatio * (1 + shiftRatio) ^ 3 < perturbation ∧
    1 + perturbation < 2 * (313 / 338 - perturbation) ∧
    (7 / 25 + perturbation) / (1 - shiftRatio) ^ 4 < 1 / 3 ∧
    (1 / 225 + 2 / 200000 : Rat) < 1 / 210 := by
  decide +kernel

theorem xi_real_resolvent_constants :
    (9 / 4 + 1 : Rat) < 13 ^ 2 ∧
    ((1 / 2 : Rat) - (13 / 8) / 5) / (5 / 2) > 1 / 16 ∧
    ((1 / 2 : Rat) + 2 / 5) / 2 < 1 / 2 ∧
    8 * (1 / 2 : Rat) / 128 = 1 / 32 := by
  decide +kernel

theorem xi_bernstein_low_exponent_constants :
    let cosine := (444 / 445 : Rat)
    let damping := (9977 / 10000 : Rat)
    let scale := (9 / 800 : Rat)
    let a := (9 / 4 : Rat)
    let endRatio := fun pole : Rat =>
      (pole / 225) * ((1 - damping * a / 225) / (1 - a / pole)) ^ 91
    (1 - damping ^ 2) * scale < 2 * (cosine - damping) ∧
    92 * damping * a / 225 < 1 ∧
    endRatio 200 < 4997 / 5000 ∧ endRatio 210 < 4997 / 5000 ∧
    (800 / 791 : Rat) ^ 91 < 3 ∧
    (7000 * (1 - 4997 / 5000) : Rat) = 21 / 5 ∧
    (3 * (210 / 40) / 16 : Rat) < 1 := by
  decide +kernel

theorem xi_bernstein_high_exponent_constants :
    let cap := (4 / 9 : Rat)
    (2 / 5 : Rat) < cap - 1 / 200 ∧
    (9 / 800 : Rat) < 1 / 2 ∧
    (9 / 800 : Rat) < 2 * (99 / 100) - 1 ∧
    (40 * cap : Rat) < 4096 ∧
    (32 / 4096 : Rat) < 1 / (160 * cap) ∧
    12 * (160 * cap) ^ 5 < 4096 ^ 3 := by
  decide +kernel

theorem xi_vertical_resolvent_constants :
    (1 + 7 / 10 + (7 / 10) ^ 2 / 2 + (7 / 10) ^ 3 / 6 : Rat) > 2 ∧
    ((7 / 10) / 4 + (7 / 10 + 1) / 2 : Rat) < 11 / 10 ∧
    (7 / 10 + 1 / 2 + 7 / 10 + 11 / 10 : Rat) = 3 ∧
    ∀ logarithm : Rat, 12 ≤ logarithm →
      (40 * logarithm + 220) / 512 < logarithm / 8 := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro logarithm height
  grind

open Lean.Grind in
theorem xi_paired_phase_numerator {K : Type _} [CommRing K] (u q r : K) :
    q * (u ^ 2 + r ^ 2) - u * (q ^ 2 + r ^ 2) = (u - q) * (u * q - r ^ 2) := by
  grind

theorem xi_bernstein_quadratic_constants :
    (6 / 169 : Rat) < 1 / 20 ∧
    (108 / 8192 ^ 2 : Rat) < 1 ∧
    (5 + 22 : Rat) < 32 ∧
    (24 * 16 / 8192 + 1056 / (8192 ^ 2 * 2 ^ 19) : Rat) < 1 / 2 ∧
    (256 * 512 * 3 ^ 4 : Rat) < 2 ^ 24 ∧
    (84 * 3 / 2 ^ 64 : Rat) < 1 / 2 ^ 30 ∧
    (2 * (4 / (1 - 1 / 4) + (1 / 4) / (1 - 1 / 4) ^ 2) : Rat) < 16 ∧
    (20 + 3 * 12 * 16 : Rat) < 600 ∧
    (600 / 2 ^ 1024 : Rat) < 1 / 2 ^ 30 ∧
    (2 / 2 ^ 30 : Rat) < 1 / 2 ^ 24 := by
  decide +kernel

open Lean.Grind in
theorem xi_ray_resolvent_factor {K : Type _} [CommRing K]
    (pole inverse scale : K) (inverseRead : pole * inverse = 1) (p q : Nat) :
    pole ^ (p + q) * (inverse ^ q * (1 - scale * inverse) ^ p) = (pole - scale) ^ p := by
  have shift : pole * (1 - scale * inverse) = pole - scale := by
    calc
      _ = pole - scale * (pole * inverse) := by grind
      _ = _ := by rw [inverseRead, Semiring.mul_one]
  calc
    _ = (pole * inverse) ^ q * (pole * (1 - scale * inverse)) ^ p := by
      rw [Semiring.pow_add, CommSemiring.mul_pow pole inverse,
        CommSemiring.mul_pow pole (1 - scale * inverse)]
      grind
    _ = _ := by rw [inverseRead, shift, Semiring.one_pow, Semiring.one_mul]

theorem xi_ray_amplitude_gap (scale realPart imaginaryPart magnitude : Rat)
    (positive : 0 < scale) (nonreal : realPart < magnitude)
    (square : magnitude ^ 2 = realPart ^ 2 + imaginaryPart ^ 2) :
    (1 - scale * magnitude) ^ 2 < (1 - scale * realPart) ^ 2 + (scale * imaginaryPart) ^ 2 := by
  have excess := Rat.mul_pos positive (show 0 < magnitude - realPart by grind)
  have identity :
      (1 - scale * realPart) ^ 2 + (scale * imaginaryPart) ^ 2 -
          (1 - scale * magnitude) ^ 2 = 2 * (scale * (magnitude - realPart)) := by
    grind
  grind

theorem xi_ray_phase_chord (value : Rat) (lower : -1 / 4 ≤ value) (upper : value ≤ 1) :
    value ^ 2 ≤ 3 * value / 4 + 1 / 4 := by
  have chord := Rat.mul_nonneg (show 0 ≤ value + 1 / 4 by grind) (show 0 ≤ 1 - value by grind)
  grind

open Lean.Grind in
theorem xi_ray_square_modulus {K : Type _} [CommRing K] (a height lateral : K) :
    (a + height ^ 2 - lateral ^ 2) ^ 2 + (2 * lateral * height) ^ 2 =
      (a + height ^ 2 + lateral ^ 2) ^ 2 - 4 * a * lateral ^ 2 := by
  grind

theorem xi_ray_strip_budget (slope : Rat) (range : 9 ≤ slope) :
    2 * (slope + 1) * slope ≤ (9 / 4) * slope ^ 2 - 1 := by
  have product := Rat.mul_nonneg (show 0 ≤ slope - 9 by grind) (show 0 ≤ slope / 4 by grind)
  have identity : (9 / 4) * slope ^ 2 - 1 - 2 * (slope + 1) * slope =
      (slope - 9) * (slope / 4) + (slope / 4 - 1) := by grind
  grind

theorem xi_ray_height_budgets :
    (144 / 49 : Rat) < 4 ∧ (9 / 4 : Rat) < 16 / 5 := by
  decide +kernel

theorem xi_ray_height_sides (center width : Rat)
    (widthNonnegative : 0 ≤ width) (room : 5 * width ≤ center) :
    (center - 2 * width) ^ 2 + width ^ 2 ≤ center ^ 2 - 3 * width * center ∧
      center ^ 2 + 3 * width * center ≤ (center + 2 * width) ^ 2 := by
  have gap := Rat.mul_nonneg widthNonnegative (show 0 ≤ center - 5 * width by grind)
  have mixed := Rat.mul_nonneg widthNonnegative (show 0 ≤ center + 4 * width by grind)
  constructor <;> grind

open Lean.Grind Std in
theorem spectral_coefficient_margin {R : Type _} [CommRing R] [LE R] [LT R]
    [IsLinearOrder R] [LawfulOrderLT R] [OrderedRing R] (u v size : R)
    (uNonnegative : 0 ≤ u) (sizeNonnegative : 0 ≤ size)
    (dominated : 4 * v ≤ u) (triangle : size ≤ u + v) :
    size * size ≤ 25 * (u * u + v * v) - 100 * (u * v) := by
  let excess := u - 4 * v
  have excessNonnegative : 0 ≤ excess := by
    dsimp [excess]
    grind
  have mixed := OrderedRing.mul_nonneg uNonnegative excessNonnegative
  have square := OrderedRing.mul_nonneg excessNonnegative excessNonnegative
  have product := OrderedRing.mul_nonneg (show 0 ≤ 5 * u - 4 * size by grind)
    (show 0 ≤ 5 * u + 4 * size by grind)
  have squareUpper : 16 * (size * size) ≤ 25 * (u * u) := by grind
  have lowerIdentity : 16 * (25 * (u * u + v * v) - 100 * (u * v)) - 25 * (u * u) =
      25 * (excess * excess) + 350 * (u * excess) := by
    dsimp [excess]
    grind
  grind

open Lean.Grind in
theorem xi_ray_repeat_factor {K : Type _} [CommRing K] (x y : K) (p q k : Nat) :
    (x ^ q * y ^ p) ^ k = x ^ (q * k) * y ^ (p * k) := by
  induction k with
  | zero => simp [Semiring.pow_zero, Semiring.one_mul]
  | succ k ih =>
    simp only [Semiring.pow_succ, ih, Nat.mul_succ, Semiring.pow_add]
    grind

theorem xi_product_budget {I : Type _} (bound anchor : I → Rat)
    (nonnegative : ∀ i, 0 ≤ bound i) (budget : ∀ i, bound i ≤ anchor i) (word : List I) :
    0 ≤ (word.map bound).prod ∧ (word.map bound).prod ≤ (word.map anchor).prod := by
  induction word with
  | nil =>
    change (0 : Rat) ≤ 1 ∧ (1 : Rat) ≤ 1
    decide
  | cons i rest ih =>
    simp only [List.map_cons, List.prod_cons]
    have anchorNonnegative := Rat.le_trans (nonnegative i) (budget i)
    exact ⟨Rat.mul_nonneg (nonnegative i) ih.1, Rat.le_trans
      (Rat.mul_le_mul_of_nonneg_right (budget i) ih.1)
      (Rat.mul_le_mul_of_nonneg_left ih.2 anchorNonnegative)⟩

open Lean.Grind Std in
theorem xi_product_moment_margin {R : Type _} [CommRing R] [LE R] [LT R]
    [IsLinearOrder R] [LawfulOrderLT R] [OrderedRing R] (anchor tail readout : R)
    (budget : 25 * tail ≤ 7 * anchor) (lower : anchor - tail ≤ readout) :
    9 * (anchor + tail) ≤ 16 * readout := by
  grind

section PowerBounds
open Lean.Grind Std
attribute [local instance] Semiring.natCast

theorem xi_ray_power_bound {R : Type _} [CommRing R] [LE R] [LT R]
    [IsLinearOrder R] [LawfulOrderLT R] [OrderedRing R] (gain bound : R)
    (archimedean : ∀ step level : R, 0 < step → ∃ k : Nat, level < (k : R) * step)
    (bounded : ∀ k : Nat, gain ^ (k + 1) ≤ bound) : gain ≤ 1 := by
  by_cases unit : gain ≤ 1
  · exact unit
  · have stepPos : 0 < gain - 1 := by grind
    have bernoulli (k : Nat) : 1 + (k : R) * (gain - 1) ≤ gain ^ k := by
      induction k with
      | zero =>
        rw [Semiring.natCast_zero, Semiring.pow_zero]
        grind
      | succ k ih =>
        have growth := OrderedRing.mul_nonneg
          (show 0 ≤ gain ^ k - (1 + (k : R) * (gain - 1)) by grind)
          (show 0 ≤ gain by grind)
        have stepSquare := OrderedRing.mul_nonneg
          (show 0 ≤ gain - 1 by grind) (show 0 ≤ gain - 1 by grind)
        have surplus := OrderedRing.mul_nonneg (show 0 ≤ (k : R) from
          OrderedRing.natCast_nonneg) stepSquare
        rw [Semiring.natCast_succ, Semiring.pow_succ]
        grind
    obtain ⟨k, crossed⟩ := archimedean (gain - 1) bound stepPos
    have lower := bernoulli (k + 1)
    rw [Semiring.natCast_succ] at lower
    have upper := bounded k
    grind

theorem xi_ray_subgeometric_bound {R : Type _} [Field R] [LE R] [LT R]
    [IsLinearOrder R] [LawfulOrderLT R] [OrderedRing R] (gain : R)
    (archimedean : ∀ step level : R, 0 < step → ∃ k : Nat, level < (k : R) * step)
    (bounded : ∀ rate : R, 1 < rate → ∃ bound : R, ∀ k : Nat,
      gain ^ (k + 1) ≤ bound * rate ^ (k + 1)) : gain ≤ 1 := by
  by_cases unit : gain ≤ 1
  · exact unit
  · let rate := (gain + 1) / 2
    have cancel (a b : R) (hb : 0 < b) : a / b * b = a := by
      rw [Field.div_eq_mul_inv, Semiring.mul_assoc, Field.inv_mul_cancel (Preorder.ne_of_gt hb),
        Semiring.mul_one]
    have middle : rate * 2 = gain + 1 := cancel _ _ (by grind)
    have aboveOne : 1 < rate := by grind
    have positive : 0 < rate := by grind
    have powersPositive (n : Nat) : 0 < rate ^ n := by
      induction n with
      | zero => rw [Semiring.pow_zero]; grind
      | succ n ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_pos ih positive
    obtain ⟨bound, upper⟩ := bounded rate aboveOne
    have normalized (k : Nat) : (gain / rate) ^ (k + 1) ≤ bound := by
      apply (Field.IsOrdered.mul_le_mul_iff_of_pos_right (powersPositive (k + 1))).mp
      rw [← CommSemiring.mul_pow, cancel gain rate positive]
      exact upper k
    have unitRatio := xi_ray_power_bound (gain / rate) bound archimedean normalized
    have compare := OrderedRing.mul_le_mul_of_nonneg_right unitRatio (Preorder.le_of_lt positive)
    rw [cancel gain rate positive, Semiring.one_mul] at compare
    grind

end PowerBounds

theorem xi_ray_sector_endpoint :
    let damping := (9977 / 10000 : Rat)
    (1 / 120 : Rat) * (1 - damping / 120) ^ 111 < (111 : Rat) ^ 111 / 112 ^ 112 := by
  decide +kernel

theorem xi_heat_tail_constants :
    let x := (19 / 4 : Rat)
    let y := (10 / 3 : Rat)
    (269 : Rat) ^ 2 + 269 < 270 ^ 2 ∧
    (4 / 3 + 1 / 15 : Rat) ^ 2 < 2 ∧
    (269 : Rat) < (33 / 2 : Rat) ^ 2 ∧
    x * (33 / 2) < (4 / 3) * (269 - 210) ∧
    8 * (270 : Rat) ^ 2 < (40 * 197) *
      (1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 / 120) ∧
    (14 / 15 + 1 / 15 : Rat) = 1 ∧
    y * (33 / 2) < (14 / 15) * (269 - 210) ∧
    3 * (270 : Rat) ^ 2 < (40 * 197) *
      (1 + y + y ^ 2 / 2 + y ^ 3 / 6 + y ^ 4 / 24 + y ^ 5 / 120 +
        y ^ 6 / 720 + y ^ 7 / 5040 + y ^ 8 / 40320) := by
  decide +kernel

open Lean.Grind in
theorem xi_heat_laplace_weights {K : Type _} [CommRing K] (pole inverse cap value : K)
    (reciprocal : pole * inverse = 1) :
    (inverse * value) ^ 2 = inverse ^ 2 * value ^ 2 ∧
    (cap * pole - 1) * (inverse * value) ^ 2 = inverse * (cap - inverse) * value ^ 2 := by
  have recover : (pole * inverse) * (cap * inverse * value ^ 2) =
      cap * inverse * value ^ 2 := by rw [reciprocal, Semiring.one_mul]
  constructor <;> grind

open Lean.Grind Std in
theorem xi_cosine_energy_weight {R : Type _} [CommRing R] [LE R] [LT R]
    [IsLinearOrder R] [LawfulOrderLT R] [OrderedRing R]
    (value cosine : R) (upper : cosine ≤ 1) :
    0 ≤ value ^ 2 - cosine * value ^ 2 := by
  have square : 0 ≤ value * value := by
    by_cases h : 0 ≤ value
    · exact OrderedRing.mul_nonneg h h
    · have opp : 0 ≤ -value := by grind
      have product := OrderedRing.mul_nonneg opp opp
      grind
  have weight := OrderedRing.mul_nonneg (show 0 ≤ 1 - cosine by grind) square
  grind

theorem xi_arithmetic_cutoff_constants :
    let r := (1 / 270 : Rat)
    (1 - 2 * (4 / 9 : Rat)) ^ 2 = 1 / 81 ∧
    r * (1 + 2 * r) < (1 / 210 : Rat) * (1 - 2 / 200) := by
  decide +kernel

theorem xi_heat_chart_actions {X Y : Type _} (encode : X → Y) (decode : Y → X)
    (leftInverse : ∀ x, decode (encode x) = x) (first second : X → X) (x : X) :
    (encode ∘ second ∘ decode) ((encode ∘ first ∘ decode) (encode x)) =
      encode (second (first x)) := by
  simp [Function.comp_def, leftInverse]

open Lean.Grind in
theorem xi_tph_haar_split {R : Type _} [CommRing R] (a b x y : R) :
    (a + b) * (a * x ^ 2 + b * y ^ 2) - (a * x + b * y) ^ 2 =
      a * b * (x - y) ^ 2 := by grind

open Lean.Grind Std in
theorem xi_tph_orthogonal_path {R : Type _} [CommRing R] [LE R] [LT R]
    [IsLinearOrder R] [LawfulOrderLT R] [OrderedRing R]
    (residual captured : Nat → R)
    (split : ∀ n, residual n = captured n + residual (n + 1))
    (cover : ∀ n, 3 * residual n ≤ 4 * captured n) (n : Nat) :
    (4 : R) ^ n * residual n ≤ residual 0 := by
  have scaleNonnegative (k : Nat) : 0 ≤ (4 : R) ^ k := by
    induction k with
    | zero => rw [Semiring.pow_zero]; grind
    | succ k ih => rw [Semiring.pow_succ]; exact OrderedRing.mul_nonneg ih (by grind)
  induction n with
  | zero => rw [Semiring.pow_zero, Semiring.one_mul]; grind
  | succ k ih =>
    have step : 4 * residual (k + 1) ≤ residual k := by
      have balance := split k
      have capturedBound := cover k
      grind
    have scaled := OrderedRing.mul_le_mul_of_nonneg_left step (scaleNonnegative k)
    rw [Semiring.pow_succ, Semiring.mul_assoc]
    grind

open Lean.Grind in
theorem xi_heat_harmonic_weights {R : Type _} [CommRing R] (c : R) :
    3 + 4 * c + (2 * c ^ 2 - 1) = 2 * (1 + c) ^ 2 := by grind

theorem xi_tph_base_factorial (f : Nat → Nat) (start : f 0 = 1)
    (step : ∀ m, f (m + 1) = (m + 1) * f m) (s k : Nat) :
    f s * f k ≤ f (s + k) := by
  induction k with
  | zero => simp [start]
  | succ k ih =>
    change f s * f (k + 1) ≤ f ((s + k) + 1)
    rw [step (s + k), step k]
    calc
      f s * ((k + 1) * f k) = (k + 1) * (f s * f k) := by ac_rfl
      _ ≤ (s + k + 1) * f (s + k) := Nat.mul_le_mul (by omega) ih

open Lean.Grind in
theorem xi_centered_lattice_forcing {R : Type _} [CommRing R]
    (regulator lattice background primes moment kernel : R)
    (regularized : regulator * background = kernel)
    (divisors : lattice * primes = background * background + moment) :
    (regulator * lattice) * (background - primes) =
      kernel * (lattice - background) - regulator * moment := by
  have square : regulator * (background * background) = kernel * background := by
    rw [← regularized]
    grind
  calc
    (regulator * lattice) * (background - primes) =
        (regulator * background) * lattice - regulator * (lattice * primes) := by grind
    _ = kernel * lattice - (regulator * (background * background) + regulator * moment) := by
      rw [regularized, divisors]
      grind
    _ = kernel * (lattice - background) - regulator * moment := by rw [square]; grind

open Lean.Grind in
theorem xi_causal_lattice_inverse {R : Type _} [CommRing R]
    (regulator lattice inverseLattice background kernel : R)
    (regularized : regulator * background = kernel)
    (unit : regulator + kernel = 1) (inverse : lattice * inverseLattice = 1) :
    (regulator * lattice) * ((1 + background) * inverseLattice) = 1 := by
  have left : regulator * (1 + background) = 1 := by
    calc
      regulator * (1 + background) = regulator + regulator * background := by grind
      _ = 1 := by rw [regularized, unit]
  calc
    (regulator * lattice) * ((1 + background) * inverseLattice) =
        (regulator * (1 + background)) * (lattice * inverseLattice) := by grind
    _ = 1 := by rw [left, inverse]; grind

open Lean.Grind in
theorem xi_heat_weight_transport {K X : Type _} [CommRing K]
    (first second combined state : X → K)
    (compose : ∀ x, second x * first x = combined x) (x : X) :
    second x * (first x * state x) = combined x * state x := by
  rw [← Semiring.mul_assoc, compose]

theorem xi_positive_subfamily_readback {Weight : Type _} (positive small : Weight → Prop)
    (energy : {s : Weight // positive s} → Prop) {conclusion : Prop}
    (witness : ∀ s, energy s)
    (readback : (∀ s : {s : Weight // positive s ∧ small s},
      energy ⟨s.val, s.property.1⟩) → conclusion) :
    (∀ s : {s : Weight // positive s ∧ small s}, energy ⟨s.val, s.property.1⟩) ∧
      conclusion := by
  have restricted (s : {s : Weight // positive s ∧ small s}) :
      energy ⟨s.val, s.property.1⟩ := witness _
  exact ⟨restricted, readback restricted⟩

open Lean.Grind in
theorem xi_tph_pair_transform {R : Type _} [CommRing R] (t x y : R) :
    (x + t * y) + t * (t * x - y) = (1 + t ^ 2) * x ∧
    t * (x + t * y) - (t * x - y) = (1 + t ^ 2) * y ∧
    (x + t * y) ^ 2 + (t * x - y) ^ 2 = (1 + t ^ 2) * (x ^ 2 + y ^ 2) := by
  constructor
  · grind
  · constructor <;> grind

theorem xi_packet_ratio_quotient {m n : Nat} (hm : 0 < m) :
    let g := m.gcd n
    Nat.Coprime (m / g) (n / g) ∧ (m / g) * g = m ∧ (n / g) * g = n ∧
    ∀ d e k : Nat, Nat.Coprime d e → m = d * k → n = e * k →
      k = g ∧ m / g = d ∧ n / g = e := by
  dsimp only
  have hg := Nat.gcd_pos_of_pos_left n hm
  refine ⟨Nat.coprime_div_gcd_div_gcd hg, Nat.div_mul_cancel (Nat.gcd_dvd_left m n),
    Nat.div_mul_cancel (Nat.gcd_dvd_right m n), ?_⟩
  intro d e k coprime left right
  have greatest : m.gcd n = k := by
    rw [left, right, Nat.gcd_mul_right, coprime.gcd_eq_one, Nat.one_mul]
  have hk : 0 < k := greatest ▸ hg
  rw [greatest, left, right]
  exact ⟨rfl, Nat.mul_div_cancel _ hk, Nat.mul_div_cancel _ hk⟩

open Lean.Grind in
theorem xi_packet_signed_gram {R : Type _} [CommRing R] (values : List R) :
    let sums := values.foldr (fun x (p : R × R) => (x + p.1, x * p.1 + p.2)) (0, 0)
    sums.1 = values.sum ∧
      values.sum ^ 2 = (values.map (fun x => x ^ 2)).sum + 2 * sums.2 := by
  induction values with
  | nil => simp <;> grind
  | cons x xs ih =>
    dsimp only at ih ⊢
    obtain ⟨total, square⟩ := ih
    simp only [List.foldr_cons, List.map_cons, List.sum_cons, total]
    constructor
    · trivial
    · grind

open Lean.Grind in
theorem xi_signed_block_abel {R : Type _} [CommRing R]
    (partialSum weight : Nat → R) (n : Nat) :
    ((List.range n).map (fun j => (partialSum (j + 1) - partialSum j) * weight j)).sum =
      partialSum n * weight n - partialSum 0 * weight 0 +
      ((List.range n).map (fun j => partialSum (j + 1) * (weight j - weight (j + 1)))).sum := by
  have appendOne (xs : List R) (v : R) : (xs ++ [v]).sum = xs.sum + v := by
    induction xs with
    | nil => simp <;> grind
    | cons a xs step =>
      simp only [List.cons_append, List.sum_cons, step]
      grind
  induction n with
  | zero => simp <;> grind
  | succ n ih =>
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil, appendOne, ih]
    grind

open Lean.Grind in
/-- Finite signed Gram difference used in the classical fiber's local window estimate. -/
theorem xi_packet_gram_compression {R I J : Type _} [CommRing R]
    (left : List I) (right : List J) (u p : I → R) (v q : J → R) :
    (left.map (fun i => (right.map (fun j => u i * v j - p i * q j)).sum)).sum =
      (left.map (fun i => u i - p i)).sum * (right.map v).sum +
      (left.map p).sum * (right.map (fun j => v j - q j)).sum := by
  have row (i : I) (ys : List J) :
      (ys.map (fun j => u i * v j - p i * q j)).sum =
        (u i - p i) * (ys.map v).sum + p i * (ys.map (fun j => v j - q j)).sum := by
    induction ys with
    | nil => simp <;> grind
    | cons j js ih =>
      simp only [List.map_cons, List.sum_cons, ih]
      grind
  induction left with
  | nil => simp <;> grind
  | cons i xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, row i right]
    grind

end GAlgebra
