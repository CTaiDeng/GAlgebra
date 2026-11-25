import GAlgebra.Targets
import GAlgebra.FiniteGeometry

set_option autoImplicit false
namespace GAlgebra

inductive OrderedTailTree where
  | leaf
  | graft : OrderedTailTree → OrderedTailTree → OrderedTailTree

namespace OrderedTailTree

def forks : OrderedTailTree → Nat
  | leaf => 0
  | graft left right => left.forks + right.forks + 1

def eval {X : Type _} (seed : X) (combine : X → X → X) : OrderedTailTree → X
  | leaf => seed
  | graft left right => combine (left.eval seed combine) (right.eval seed combine)

theorem eval_transport {X Y : Type _} (transport : X → Y)
    (seed : X) (source : X → X → X) (target : Y → Y → Y)
    (law : ∀ a b, transport (source a b) = target (transport a) (transport b))
    (tree : OrderedTailTree) :
    transport (tree.eval seed source) = tree.eval (transport seed) target := by
  induction tree with
  | leaf => rfl
  | graft left right leftLaw rightLaw =>
    simp only [eval, law, leftLaw, rightLaw]

theorem eval_grade {X : Type _} (grade : Nat → X → Prop)
    (seed : X) (combine : X → X → X) (seedGrade : grade 1 seed)
    (law : ∀ n m a b, grade n a → grade m b → grade (n + m) (combine a b))
    (tree : OrderedTailTree) :
    grade (tree.forks + 1) (tree.eval seed combine) := by
  induction tree with
  | leaf => exact seedGrade
  | graft left right leftGrade rightGrade =>
    have leaves : (left.forks + 1) + (right.forks + 1) = (graft left right).forks + 1 := by
      simp only [forks]
      omega
    rw [← leaves]
    exact law _ _ _ _ leftGrade rightGrade

theorem eval_le {X : Type _} (size : X → Rat)
    (seed : X) (combine : X → X → X) (s M : Rat)
    (nonnegSize : ∀ a, 0 ≤ size a) (nonnegM : 0 ≤ M)
    (base : size seed ≤ s)
    (bilinear : ∀ a b, size (combine a b) ≤ M * size a * size b)
    (tree : OrderedTailTree) : size (tree.eval seed combine) ≤ s * (M * s) ^ tree.forks := by
  induction tree with
  | leaf => simpa only [eval, forks, Rat.pow_zero, Rat.mul_one] using base
  | graft left right leftBound rightBound =>
    let a := left.eval seed combine
    let b := right.eval seed combine
    have scaled := Rat.mul_le_mul_of_nonneg_left leftBound nonnegM
    have leftProduct := Rat.mul_le_mul_of_nonneg_right scaled (nonnegSize b)
    have nonnegLeft : 0 ≤ M * (s * (M * s) ^ left.forks) :=
      Rat.le_trans (Rat.mul_nonneg nonnegM (nonnegSize a)) scaled
    have rightProduct := Rat.mul_le_mul_of_nonneg_left rightBound nonnegLeft
    calc
      _ ≤ M * size a * size b := bilinear a b
      _ ≤ M * (s * (M * s) ^ left.forks) * size b := leftProduct
      _ ≤ M * (s * (M * s) ^ left.forks) * (s * (M * s) ^ right.forks) := rightProduct
      _ = _ := by
        simp only [forks, Rat.pow_succ, Lean.Grind.Semiring.pow_add]
        grind

end OrderedTailTree

structure QuadraticTailLaw (Z : Type _) [Add Z] where
  seed : Z
  combine : Z → Z → Z
  size : Z → Rat
  seedCap : Rat
  quadraticCap : Rat
  radius : Rat
  nonnegativeSize : ∀ z, 0 ≤ size z
  nonnegativeCap : 0 ≤ quadraticCap
  nonnegativeRadius : 0 ≤ radius
  seedBound : size seed ≤ seedCap
  combineBound : ∀ z w, size (combine z w) ≤ quadraticCap * size z * size w
  room : seedCap + quadraticCap * radius ^ 2 ≤ radius
  tailResidualZero : Z → Prop
  readback : ∀ z, size z ≤ radius → z = seed + combine z z → tailResidualZero z

namespace QuadraticTailLaw

def Legal {Z : Type _} [Add Z] (law : QuadraticTailLaw Z) (z : Z) : Prop :=
  law.size z ≤ law.radius

theorem eval_legal {Z : Type _} [Add Z] (law : QuadraticTailLaw Z) (tree : OrderedTailTree) :
    law.Legal (tree.eval law.seed law.combine) := by
  have seedCapNonneg := Rat.le_trans (law.nonnegativeSize law.seed) law.seedBound
  have quadraticNonneg := Rat.mul_nonneg
    (Rat.mul_nonneg law.nonnegativeCap law.nonnegativeRadius) law.nonnegativeRadius
  have room := law.room
  simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul] at room
  induction tree with
  | leaf =>
    exact Rat.le_trans law.seedBound (by grind)
  | graft left right leftLegal rightLegal =>
    let a := left.eval law.seed law.combine
    let b := right.eval law.seed law.combine
    have leftBound : law.size a ≤ law.radius := leftLegal
    have rightBound : law.size b ≤ law.radius := rightLegal
    have leftMultiply := Rat.mul_le_mul_of_nonneg_left leftBound law.nonnegativeCap
    have leftProduct := Rat.mul_le_mul_of_nonneg_right leftMultiply (law.nonnegativeSize b)
    have rightProduct := Rat.mul_le_mul_of_nonneg_left rightBound
      (Rat.mul_nonneg law.nonnegativeCap law.nonnegativeRadius)
    calc
      law.size (law.combine a b) ≤ law.quadraticCap * law.size a * law.size b :=
        law.combineBound a b
      _ ≤ law.quadraticCap * law.radius * law.size b := leftProduct
      _ ≤ law.quadraticCap * law.radius * law.radius := rightProduct
      _ ≤ law.radius := by grind

end QuadraticTailLaw

theorem periodic_tail_residual_identity {Z : Type _} [Abelian Z] (linear : AddMap Z Z)
    (z h value defect quadratic : Z)
    (seedRead : linear h = -defect) (combineRead : linear value = -quadratic) :
    defect + (linear z + quadratic) = linear (z + -h + -value) := by
  calc
    _ = (linear z + defect) + quadratic := by
      rw [← Abelian.assoc, Abelian.comm defect (linear z)]
    _ = _ := by
      simp only [linear.map_add, linear.map_neg, seedRead, combineRead, Abelian.neg_neg]

theorem periodic_projected_quadratic {Z W : Type _} [Abelian Z] [Abelian W]
    (project : AddMap Z W) (quadratic : Z → Z → Z) (e w : Z)
    (addLeft : ∀ a b c, quadratic (a + b) c = quadratic a c + quadratic b c)
    (addRight : ∀ a b c, quadratic a (b + c) = quadratic a b + quadratic a c)
    (hidden : project w = 0) :
    project (e + w + quadratic (e + w) (e + w)) =
      project (e + quadratic e e) +
        (project (quadratic e w) + (project (quadratic w e) + project (quadratic w w))) := by
  simp only [addLeft, addRight, project.map_add, hidden, Abelian.assoc, Abelian.zero_add]

theorem periodic_finite_reduction_readback {Z : Type _} [Abelian Z]
    (project : AddMap Z Z) (z e response : Z)
    (tail : z + (response + -(project response)) = e) :
    z + response = e + project response ∧
      e + -(project z) =
        (e + project response) + -(project (e + project response)) := by
  have full : z + response = e + project response := by
    calc
      _ = (z + (response + -(project response))) + project response := by
        simp only [Abelian.assoc, Abelian.neg_add, Abelian.add_zero]
      _ = _ := by rw [tail]
  refine ⟨full, ?_⟩
  calc
    _ = (e + project response) + -(project z + project response) := by
      rw [Abelian.neg_add_rev, Abelian.assoc e (project response),
        ← Abelian.assoc (project response) (-(project response)), Abelian.add_neg, Abelian.zero_add]
    _ = _ := by rw [← project.map_add, full]

theorem periodic_finite_test_preserved {Z W : Type _} [Abelian Z] [Abelian W]
    (project : AddMap Z Z) (read : AddMap Z W) (z e response : Z)
    (fixed : ∀ v, read (project v) = read v)
    (tail : z + (response + -(project response)) = e) :
    read z = read e := by
  simpa only [read.map_add, read.map_neg, fixed, Abelian.add_neg, Abelian.add_zero]
    using congrArg (fun v => read v) tail

theorem periodic_mean_read_preserved {Z : Type _} [Abelian Z]
    (project : AddMap Z Z) (read : AddMap Z Rat) (write : AddMap Rat Z)
    (projector : ∀ v, project (project v) = project v)
    (readWrite : ∀ a, read (write a) = a)
    (writeInRange : ∀ a, project (write a) = write a) :
    let corrected := fun v => project v + write (read (v + -(project v)))
    (∀ v, read (corrected v) = read v) ∧
    (∀ v, project (corrected v) = corrected v) ∧
    (∀ v, corrected (project v) = project v) := by
  dsimp
  refine ⟨?_, ?_, ?_⟩
  · intro v
    rw [read.map_add, readWrite, read.map_add, read.map_neg]
    grind
  · intro v
    rw [project.map_add, projector, writeInRange]
  · intro v
    rw [projector, Abelian.add_neg, read.map_zero, write.map_zero, Abelian.add_zero]

theorem periodic_mean_feedback_readback {X Y : Type _} [Abelian X] [Abelian Y]
    (response : AddMap X Y) (lift : AddMap Y X) (base : X) (defect shift : Y)
    (balanced : response base = 0)
    (rightInverse : ∀ r, response (lift r) = r) :
    defect + response (base + lift (shift + -defect)) = shift := by
  rw [response.map_add, balanced, Abelian.zero_add, rightInverse,
    Abelian.comm shift (-defect), ← Abelian.assoc, Abelian.add_neg, Abelian.zero_add]

theorem periodic_separated_feedback_readback {Z Y W : Type _}
    [Abelian Z] [Abelian Y] [Abelian W]
    (meanRead : AddMap Z Y) (firstRead : AddMap Z W)
    (meanResponse firstResponse remainder : Z) (meanTarget : Y) (firstTarget : W)
    (meanOnMean : meanRead meanResponse = meanTarget)
    (meanOnFirst : meanRead firstResponse = 0)
    (firstOnMean : firstRead meanResponse = 0)
    (firstOnFirst : firstRead firstResponse = firstTarget) :
    meanRead (meanResponse + firstResponse + remainder) = meanTarget + meanRead remainder ∧
      firstRead (meanResponse + firstResponse + remainder) = firstTarget + firstRead remainder := by
  constructor
  · simp only [meanRead.map_add, meanOnMean, meanOnFirst, Abelian.add_zero]
  · simp only [firstRead.map_add, firstOnMean, firstOnFirst, Abelian.zero_add]

theorem periodic_shape_diagonal_readback {Z : Type _} [Abelian Z]
    (project : AddMap Z Z) (scale : Rat → Z → Z)
    (shape tail response residual : Z) (coefficient : Rat)
    (scaleAdd : ∀ a b, scale coefficient (a + b) = scale coefficient a + scale coefficient b)
    (finitePart : project response = scale coefficient shape + residual)
    (tailPart : response + -(project response) = scale coefficient tail) :
    response = scale coefficient (shape + tail) + residual := by
  calc
    response = (response + -(project response)) + project response := by
      rw [Abelian.assoc, Abelian.neg_add, Abelian.add_zero]
    _ = scale coefficient tail + (scale coefficient shape + residual) := by
      rw [tailPart, finitePart]
    _ = scale coefficient (shape + tail) + residual := by
      rw [← Abelian.assoc, Abelian.comm (scale coefficient tail) (scale coefficient shape),
        ← scaleAdd]

theorem periodic_shape_amplitude (initial correction : Rat)
    (negative : initial < 0) (preservedSign : -1 < correction) :
    let coefficient := initial * (1 + correction)
    let amplitude := (-1) / coefficient
    0 < amplitude ∧ amplitude + amplitude ^ 2 * coefficient = 0 := by
  let coefficient := initial * (1 + correction)
  let amplitude := (-1) / coefficient
  change 0 < amplitude ∧ amplitude + amplitude ^ 2 * coefficient = 0
  have coefficientNegative : coefficient < 0 := by
    have scaled := Rat.mul_lt_mul_of_pos_right negative (show 0 < 1 + correction by grind)
    dsimp [coefficient]
    grind
  have product : amplitude * coefficient = -1 :=
    Rat.div_mul_cancel (Rat.ne_of_lt coefficientNegative)
  constructor
  · by_cases positive : 0 < amplitude
    · exact positive
    · have scaled := Rat.mul_le_mul_of_nonneg_right (show amplitude ≤ 0 by grind)
        (show 0 ≤ -coefficient by grind)
      grind
  · calc
      _ = amplitude + amplitude * (amplitude * coefficient) := by grind
      _ = 0 := by rw [product]; grind

theorem periodic_shape_denominator (observed cap error diagonal : Rat)
    (observedPositive : 0 < observed) (observedUpper : observed ≤ cap)
    (errorUpper : error ≤ observed / 2)
    (readUpper : observed ^ 2 * diagonal ≤ -observed + error) :
    diagonal ≤ (-1) / (2 * cap) := by
  have onObserved : diagonal * (2 * observed) ≤ -1 := by
    apply Rat.le_of_mul_le_mul_right _ observedPositive
    have doubled := Rat.mul_le_mul_of_nonneg_left readUpper (show 0 ≤ (2 : Rat) by decide)
    grind
  have diagonalNonpositive : diagonal ≤ 0 := by
    by_cases positive : 0 < diagonal
    · have product := Rat.mul_pos positive (show 0 < 2 * observed by grind)
      grind
    · grind
  have scaled := Rat.mul_le_mul_of_nonneg_left (show 2 * observed ≤ 2 * cap by grind)
    (show 0 ≤ -diagonal by grind)
  have capPositive : 0 < 2 * cap := by grind
  apply Rat.le_of_mul_le_mul_right _ capPositive
  rw [Rat.div_mul_cancel (Rat.ne_of_gt capPositive)]
  grind

theorem periodic_shape_tree_gate (lower seed linear quadratic radius : Rat)
    (quadraticNonnegative : 0 ≤ quadratic) (radiusNonnegative : 0 ≤ radius)
    (room : seed + linear * radius + quadratic * radius ^ 2 ≤ lower * radius)
    (slope : linear + 2 * quadratic * radius < lower) :
    let gap := lower - linear
    let s := seed / gap
    let M := quadratic / gap
    0 < gap ∧ s + M * radius ^ 2 ≤ radius ∧
      2 * M * radius < 1 ∧ 4 * M * s < 1 := by
  let gap := lower - linear
  have productNonnegative := Rat.mul_nonneg quadraticNonnegative radiusNonnegative
  have gapPositive : 0 < gap := by
    dsimp [gap]
    grind
  let s := seed / gap
  let M := quadratic / gap
  have seedRead : s * gap = seed := Rat.div_mul_cancel (Rat.ne_of_gt gapPositive)
  have quadRead : M * gap = quadratic := Rat.div_mul_cancel (Rat.ne_of_gt gapPositive)
  have nonnegative : 0 ≤ M :=
    Rat.le_of_mul_le_mul_right (by simpa [quadRead] using quadraticNonnegative) gapPositive
  have roomScaled : (s + M * radius ^ 2) * gap ≤ radius * gap := by
    calc
      _ = seed + quadratic * radius ^ 2 := by grind
      _ ≤ radius * gap := by dsimp [gap]; grind
  have roomSmall := Rat.le_of_mul_le_mul_right roomScaled gapPositive
  have slopeScaled : (2 * M * radius) * gap < 1 * gap := by
    calc
      _ = 2 * quadratic * radius := by grind
      _ < 1 * gap := by dsimp [gap]; grind
  have slopeSmall := Rat.lt_of_mul_lt_mul_right slopeScaled (Rat.le_of_lt gapPositive)
  have bound := Rat.mul_le_mul_of_nonneg_left roomSmall (show 0 ≤ 4 * M by grind)
  have squarePositive := Rat.mul_pos (show 0 < 1 - 2 * M * radius by grind)
    (show 0 < 1 - 2 * M * radius by grind)
  refine ⟨gapPositive, roomSmall, slopeSmall, ?_⟩
  simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul] at bound
  grind

theorem periodic_even_paired_degree (pairs : List (Int × Int))
    (unit : ∀ p ∈ pairs, (p.1 = 1 ∨ p.1 = -1) ∧ (p.2 = 1 ∨ p.2 = -1)) :
    ∃ degree : Int, (pairs.map (fun p => p.1 + p.2)).sum = 2 * degree := by
  induction pairs with
  | nil => exact ⟨0, rfl⟩
  | cons p rest ih =>
    obtain ⟨degree, count⟩ := ih (fun q h => unit q (List.mem_cons_of_mem p h))
    obtain ⟨first, second⟩ := unit p (by simp)
    refine ⟨(p.1 + p.2) / 2 + degree, ?_⟩
    simp only [List.map_cons, List.sum_cons, count]
    rcases first with sign | sign <;> rcases second with sign' | sign' <;> omega

theorem periodic_read_projection {Z Coordinates : Type _}
    (read : Z → Coordinates) (lift : Coordinates → Z)
    (readLift : ∀ a, read (lift a) = a) :
    let project := fun z => lift (read z)
    (∀ z, read (project z) = read z) ∧ (∀ z, project (project z) = project z) := by
  refine ⟨fun z => readLift (read z), ?_⟩
  intro z
  change lift (read (lift (read z))) = lift (read z)
  rw [readLift]

open Lean.Grind in
theorem periodic_two_mode_resultant {K : Type _} [CommRing K]
    (A B C beta gamma x y : K) :
    beta ^ 2 * (A * x ^ 2 + B * x * y + C * y ^ 2) -
        (beta * x + gamma * y) * (A * (beta * x - gamma * y) + B * beta * y) =
      (A * gamma ^ 2 - B * beta * gamma + C * beta ^ 2) * (y * y) := by
  grind

open Lean.Grind in
theorem periodic_two_mode_common_zero_iff {K : Type _} [Field K]
    (A B C beta gamma : K) (gainNonzero : beta ≠ 0) :
    let resultant := A * gamma ^ 2 - B * beta * gamma + C * beta ^ 2
    (∀ x y : K, A * x ^ 2 + B * x * y + C * y ^ 2 = 0 →
        x * (beta * x + gamma * y) = 0 → x = 0 ∧ y = 0) ↔
      C ≠ 0 ∧ resultant ≠ 0 := by
  let resultant := A * gamma ^ 2 - B * beta * gamma + C * beta ^ 2
  constructor
  · intro separates
    constructor
    · intro cZero
      have point := separates 0 1 (by grind) (by grind)
      exact Field.zero_ne_one point.2.symm
    · intro resultantZero
      have first : A * (-gamma) ^ 2 + B * (-gamma) * beta + C * beta ^ 2 = 0 := by
        grind
      have point := separates (-gamma) beta first (by grind)
      exact gainNonzero point.2
  · rintro ⟨cNonzero, resultantNonzero⟩ x y first second
    rcases Field.of_mul_eq_zero second with xZero | line
    · have product : C * (y * y) = 0 := by
        rw [xZero] at first
        grind
      have square := (Field.of_mul_eq_zero product).resolve_left cNonzero
      exact ⟨xZero, (Field.of_mul_eq_zero square).elim id id⟩
    · have product : resultant * (y * y) = 0 := by
        calc
          _ = beta ^ 2 * (A * x ^ 2 + B * x * y + C * y ^ 2) -
              (beta * x + gamma * y) * (A * (beta * x - gamma * y) + B * beta * y) :=
            (periodic_two_mode_resultant A B C beta gamma x y).symm
          _ = 0 := by rw [first, line]; grind
      have square := (Field.of_mul_eq_zero product).resolve_left resultantNonzero
      have yZero := (Field.of_mul_eq_zero square).elim id id
      have productX : beta * x = 0 := by rw [yZero] at line; grind
      exact ⟨(Field.of_mul_eq_zero productX).resolve_left gainNonzero, yZero⟩

theorem periodic_lifted_mode_separation (j k : Int)
    (first : j = -5 ∨ j = -2 ∨ j = 2 ∨ j = 5)
    (second : k = -5 ∨ k = -2 ∨ k = 2 ∨ k = 5) :
    (j + k ≠ 2 ∧ j + k ≠ -2) ∧
      (j + k = 10 ↔ j = 5 ∧ k = 5) ∧
      (j + k = -10 ↔ j = -5 ∧ k = -5) := by
  omega

theorem periodic_lifted_cross_modes (j k : Int)
    (secondMode : j = -2 ∨ j = 2) (fifthMode : k = -5 ∨ k = 5) :
    j + k = -7 ∨ j + k = -3 ∨ j + k = 3 ∨ j + k = 7 := by
  omega

open Lean.Grind in
theorem periodic_readout_calibration {K : Type _} [Field K]
    (base gain target : K) (nonzero : gain ≠ 0) :
    base + ((target - base) / gain) * gain = target := by
  rw [Field.div_mul_cancel nonzero]
  grind

theorem periodic_calibrated_resultant (gap gain : Rat) (positive : 0 < gain) :
    let target := 1 + max 0 gap / gain
    1 ≤ target ∧ gain ≤ gain * target - gap := by
  dsimp only
  have nonnegative : 0 ≤ max 0 gap := by
    rw [Rat.max_def]
    split <;> grind
  have upper : gap ≤ max 0 gap := by
    rw [Rat.max_def]
    split <;> grind
  have correction : 0 ≤ max 0 gap / gain := by
    rw [Rat.div_def]
    exact Rat.mul_nonneg nonnegative (Rat.le_of_lt (Rat.inv_pos.mpr positive))
  have scaled := periodic_readout_calibration 0 gain (max 0 gap) (show gain ≠ 0 by grind)
  constructor
  · grind
  · calc
      gain ≤ gain + max 0 gap - gap := by grind
      _ = _ := by grind

open Lean.Grind in
theorem periodic_tail_budget_difference {K : Type _} [CommRing K]
    (gap quadratic cubic optimum radius : K)
    (balanced : gap = 2 * quadratic * optimum + 3 * cubic * optimum ^ 2) :
    (gap * optimum - quadratic * optimum ^ 2 - cubic * optimum ^ 3) -
      (gap * radius - quadratic * radius ^ 2 - cubic * radius ^ 3) =
        (radius - optimum) ^ 2 * (quadratic + cubic * (2 * optimum + radius)) := by
  rw [balanced]
  grind

open Lean.Grind in
theorem periodic_tail_gate_slack {K : Type _} [CommRing K]
    (gap finiteMixed tailQuadratic finiteQuadratic optimum : K)
    (balanced : gap = 2 * (finiteMixed + tailQuadratic) * optimum +
      3 * finiteQuadratic * optimum ^ 2) :
    gap - (finiteMixed + 2 * tailQuadratic) * optimum - finiteQuadratic * optimum ^ 2 =
      finiteMixed * optimum + 2 * finiteQuadratic * optimum ^ 2 := by
  rw [balanced]
  grind

open Lean.Grind in
theorem periodic_tail_cubic_scale {K : Type _} [CommRing K] (curvature radius : K) :
    27 * curvature * (2 * curvature * radius ^ 3) ^ 2 = 4 * (3 * curvature * radius ^ 2) ^ 3 := by
  grind

open Lean.Grind in
theorem periodic_lift_calibration_scale {K : Type _} [Field K]
    (target original fifthRead lift gain : K) (nonzero : lift ^ 2 * gain ≠ 0) :
    (fifthRead + (target - original - lift ^ 2 * fifthRead) / (lift ^ 2 * gain) * gain) * lift ^ 2 =
      target - original := by
  calc
    _ = fifthRead * lift ^ 2 +
          ((target - original - lift ^ 2 * fifthRead) / (lift ^ 2 * gain)) * (lift ^ 2 * gain) := by
      grind
    _ = _ := by
      rw [Field.div_mul_cancel nonzero]
      grind

theorem periodic_unit_shape_budget (x y : Rat) (unit : x + y = 1) :
    x ^ 2 + 2 * x * y + y ^ 2 = 1 := by
  calc
    _ = (x + y) ^ 2 := by grind
    _ = 1 := by rw [unit]; decide +kernel

theorem periodic_high_mixed_frequency (j k : Int) (M : Nat)
    (low : j.natAbs ≤ 5) (high : M < k.natAbs) (cutoff : 15 ≤ M) :
    M - 4 ≤ (j + k).natAbs ∧ 10 < (j + k).natAbs := by
  have addBack : j + k + (-j) = k := by omega
  have reverse : k.natAbs ≤ (j + k).natAbs + j.natAbs := by
    simpa only [addBack, Int.natAbs_neg] using Int.natAbs_add_le (j + k) (-j)
  omega

theorem periodic_mode_cancellation_gap (j k : Int) (M m : Nat)
    (cutoff : m ≤ M) (high : M < j.natAbs) (low : (j + k).natAbs ≤ m) :
    2 * (M + 1 - m) ≤ j.natAbs + k.natAbs - (j + k).natAbs := by
  have addBack : j + k + (-k) = j := by omega
  have reverse : j.natAbs ≤ (j + k).natAbs + k.natAbs := by
    simpa only [addBack, Int.natAbs_neg] using Int.natAbs_add_le (j + k) (-k)
  omega

theorem periodic_weighted_block_bound (low high lowMass highMass lowBudget highBudget : Rat)
    (lowNonnegative : 0 ≤ lowMass) (highNonnegative : 0 ≤ highMass)
    (lowBound : low ≤ lowBudget * lowMass) (highBound : high ≤ highBudget * highMass) :
    low + high ≤ max lowBudget highBudget * (lowMass + highMass) := by
  rw [Rat.max_def]
  split
  · rename_i ordered
    have scaled := Rat.mul_le_mul_of_nonneg_right ordered lowNonnegative
    grind
  · rename_i swapped
    have scaled := Rat.mul_le_mul_of_nonneg_right
      (show highBudget ≤ lowBudget by grind) highNonnegative
    grind

theorem periodic_even_shape_coarse_constants :
    (1 - (2 + 1 / 4) / 4 : Rat) = 7 / 16 ∧
    (1 / 16 : Rat) * (5 / 4) ^ 2 < (1 / 4) * (7 / 16) ∧
    (2 / 16 : Rat) * (5 / 4) < 7 / 16 := by
  decide +kernel

theorem periodic_rotation_generator_difference {Pressure Velocity Curl : Type _}
    [Abelian Pressure] [Abelian Velocity] [Abelian Curl]
    (complex : TwoStep Pressure Velocity Curl) (common first second : Velocity)
    (p p' : Pressure) (original : common + first + complex.up p = 0)
    (transported : common + second + complex.up p' = 0) :
    complex.down (second + -first) = 0 := by
  have old := congrArg complex.down original
  have new := congrArg complex.down transported
  simp only [complex.down.map_add, complex.square, Abelian.add_zero, complex.down.map_zero] at old new
  have same := Abelian.cancel_left (new.trans old.symm)
  rw [complex.down.map_add, complex.down.map_neg, same, Abelian.add_neg]

open Lean.Grind in
theorem periodic_quarter_turn_difference {K : Type _} [CommRing K] (x y : K) :
    (-y - x) * (-y - x) + (x - y) * (x - y) = 2 * (x * x + y * y) := by
  grind

theorem periodic_high_harmonic_balance (baseline correction tail linear source : Rat)
    (equation : baseline * tail - linear = source - baseline * correction * tail) :
    linear + source = baseline * (1 + correction) * tail := by
  grind

theorem periodic_first_harmonic_gap (gap bound size leading error residual : Rat)
    (linearLower : gap * size ≤ leading)
    (cubicUpper : error ≤ bound * size ^ 3)
    (reverseTriangle : leading ≤ residual + error) :
    (gap - bound * size ^ 2) * size ≤ residual := by
  simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul] at cubicUpper ⊢
  grind

theorem periodic_tail_defect_bound (distance defect rate : Rat)
    (positiveGap : 0 < 1 - rate)
    (differenceBound : distance ≤ defect + rate * distance) :
    distance ≤ defect / (1 - rate) := by
  apply Rat.le_of_mul_le_mul_right _ positiveGap
  rw [Rat.div_mul_cancel (Rat.ne_of_gt positiveGap)]
  grind

theorem periodic_trace_energy_readback
    (initial terminal dissipation ratio observed transportError tailError : Rat)
    (positiveGap : 0 < 1 - ratio)
    (seam : terminal = ratio * initial) (spend : initial - terminal = dissipation)
    (readUpper : initial ≤ observed + transportError + tailError) :
    dissipation = (1 - ratio) * initial ∧
      dissipation / (1 - ratio) ≤ observed + transportError + tailError := by
  have balance : dissipation = (1 - ratio) * initial := by grind
  constructor
  · exact balance
  · apply Rat.le_of_mul_le_mul_right _ positiveGap
    rw [Rat.div_mul_cancel (Rat.ne_of_gt positiveGap)]
    have scaled := Rat.mul_le_mul_of_nonneg_right readUpper (Rat.le_of_lt positiveGap)
    grind

theorem periodic_trace_tensor_radial (trace quadratic : Rat) :
    3 * (trace + 2 * quadratic) - 15 * quadratic = 3 * trace - 9 * quadratic := by
  grind

theorem periodic_trace_tensor_off_diagonal (diagonalFirst diagonalSecond offDiagonal : Rat) :
    (diagonalFirst + diagonalSecond + 2 * offDiagonal) / 2 -
      (diagonalFirst + diagonalSecond) / 2 = offDiagonal := by
  grind

theorem periodic_trace_rotation_norm (a q cosine sine x y : Rat)
    (unitCircle : cosine ^ 2 + sine ^ 2 = 1) :
    ((a - q * cosine) * x + q * sine * y) ^ 2 +
        ((a - q * cosine) * y - q * sine * x) ^ 2 =
      (a ^ 2 + q ^ 2 - 2 * a * q * cosine) * (x ^ 2 + y ^ 2) := by
  calc
    _ = (a ^ 2 + q ^ 2 * (cosine ^ 2 + sine ^ 2) - 2 * a * q * cosine) *
          (x ^ 2 + y ^ 2) := by grind
    _ = _ := by rw [unitCircle, Rat.mul_one]

theorem periodic_trace_rotation_minimax (q cosine : Rat) (qPositive : 0 < q) :
    let first := 1 + q ^ 2 - 2 * q * cosine
    let second := 1 + q ^ 2 - 2 * q * (2 * cosine ^ 2 - 1)
    let optimum := 1 + q + q ^ 2
    (cosine = -1 / 2 ∧ first = optimum ∧ second = optimum) ∨
      first < optimum ∨ second < optimum := by
  dsimp
  by_cases atOptimum : cosine = -1 / 2
  · exact Or.inl ⟨atOptimum, by grind, by grind⟩
  · apply Or.inr
    by_cases cosineAbove : -1 / 2 < cosine
    · apply Or.inl
      have gap := Rat.mul_pos (show 0 < 2 * q by grind)
        (show 0 < cosine + 1 / 2 by grind)
      grind
    · apply Or.inr
      have doubledGap := Rat.mul_pos (show 0 < -cosine - 1 / 2 by grind)
        (show 0 < -cosine + 1 / 2 by grind)
      have gap := Rat.mul_pos (show 0 < 2 * q by grind)
        (show 0 < (2 * cosine ^ 2 - 1) + 1 / 2 by grind)
      grind

theorem periodic_trace_three_radii (ratio leading firstTail atStart afterMove afterTwoMoves : Rat) :
    (leading + firstTail * ratio ^ 4 + ratio ^ 6 * afterTwoMoves) -
        (1 + ratio ^ 2) * (leading + firstTail * ratio ^ 2 + ratio ^ 3 * afterMove) +
        ratio ^ 2 * (leading + firstTail + atStart) =
      (ratio ^ 2 * atStart - ratio ^ 3 * afterMove) -
        ratio ^ 3 * (ratio ^ 2 * afterMove - ratio ^ 3 * afterTwoMoves) := by
  grind

theorem periodic_phase_half_order_budget (factor head near middle slow far : Rat)
    (headBound : head ≤ 2 * factor) (nearBound : near ≤ 4 * factor)
    (middleBound : middle ≤ 2 * factor) (slowBound : slow ≤ 6 * factor)
    (farBound : far ≤ 6 * factor) :
    head + near + middle + slow + far ≤ 20 * factor := by
  grind

theorem periodic_radial_heat_gap (q q' r : Rat)
    (lowerNonnegative : 0 ≤ q') (ordered : q' ≤ q) (radiusNonnegative : 0 ≤ r) :
    let gap := (1 - (q' * r)^2) - (1 - (q * r)^2)
    0 ≤ gap ∧ gap ≤ 2 * q * (q - q') * r^2 := by
  dsimp
  have radialPart : 0 ≤ (q - q') * r^2 :=
    Rat.mul_nonneg (by grind) (Rat.pow_nonneg radiusNonnegative)
  have factorization :
      (1 - (q' * r)^2) - (1 - (q * r)^2) = (q + q') * ((q - q') * r^2) := by
    grind
  rw [factorization]
  constructor
  · exact Rat.mul_nonneg (by grind) radialPart
  · have bounded := Rat.mul_le_mul_of_nonneg_right (show q + q' ≤ 2 * q by grind) radialPart
    grind

theorem periodic_phase_weight_mul (base : Rat) (baseAtLeastOne : 1 ≤ base) (j k : Int) :
    base ^ (j + k).natAbs ≤ base ^ j.natAbs * base ^ k.natAbs := by
  have baseNonnegative : 0 ≤ base := by grind
  have one_le_power (n : Nat) : 1 ≤ base ^ n := by
    induction n with
    | zero => simp [Rat.pow_zero]
    | succ n ih =>
      rw [Rat.pow_succ]
      have scaled := Rat.mul_le_mul_of_nonneg_right ih baseNonnegative
      rw [Rat.one_mul] at scaled
      exact Rat.le_trans baseAtLeastOne scaled
  obtain ⟨gap, addition⟩ := Nat.exists_eq_add_of_le (Int.natAbs_add_le j k)
  calc
    _ = base ^ (j + k).natAbs * 1 := (Rat.mul_one _).symm
    _ ≤ base ^ (j + k).natAbs * base ^ gap :=
      Rat.mul_le_mul_of_nonneg_left (one_le_power gap) (Rat.pow_nonneg baseNonnegative)
    _ = base ^ (j.natAbs + k.natAbs) := by rw [addition, Lean.Grind.Semiring.pow_add]
    _ = _ := Lean.Grind.Semiring.pow_add _ _ _

theorem periodic_projection_tail_split {Z : Type _} [Abelian Z]
    (time space : AddMap Z Z) (x : Z) :
    x + -(time (space x)) = (x + -(time x)) + time (x + -(space x)) := by
  rw [time.map_add, time.map_neg, Abelian.assoc, ← Abelian.assoc (-(time x)) (time x),
    Abelian.neg_add, Abelian.zero_add]

theorem periodic_parameter_interpolation (first second : Rat)
    (firstNonnegative : 0 ≤ first) (secondNonnegative : 0 ≤ second) :
    (min first second) ^ 3 ≤ first * second ^ 2 := by
  rw [Rat.min_def]
  by_cases ordered : first ≤ second
  · rw [ite_eq_left ordered]
    have difference := Rat.mul_nonneg (show 0 ≤ second - first by grind)
      (show 0 ≤ second + first by grind)
    have squares : first ^ 2 ≤ second ^ 2 := by grind
    have scaled := Rat.mul_le_mul_of_nonneg_left squares firstNonnegative
    grind
  · rw [ite_eq_right ordered]
    have scaled := Rat.mul_le_mul_of_nonneg_right
      (show second ≤ first by grind) (Rat.pow_nonneg (n := 2) secondNonnegative)
    grind

theorem periodic_center_inverse_budget
    (result input low tail lowProjection tailProjection coupling inverse : Rat)
    (couplingNonnegative : 0 ≤ coupling) (inverseNonnegative : 0 ≤ inverse)
    (lowBound : low ≤ lowProjection * input) (tailBound : tail ≤ tailProjection * input)
    (estimate : result ≤ tail + inverse * (low + coupling * tail)) :
    result ≤ (lowProjection * inverse + tailProjection * (1 + coupling * inverse)) * input := by
  have crossTail := Rat.mul_le_mul_of_nonneg_left tailBound couplingNonnegative
  have combined : low + coupling * tail ≤ (lowProjection + coupling * tailProjection) * input := by
    grind
  have scaled := Rat.mul_le_mul_of_nonneg_left combined inverseNonnegative
  grind

theorem periodic_center_mixed_budget (fraction : Rat) :
    256 * fraction * (1 - fraction) ^ 3 ≤ 27 := by
  have squareNonnegative (value : Rat) : 0 ≤ value ^ 2 := by
    by_cases nonnegative : 0 ≤ value
    · exact Rat.pow_nonneg nonnegative
    · have opposite := Rat.pow_nonneg (n := 2) (show 0 ≤ -value by grind)
      grind
  have product := Rat.mul_nonneg (squareNonnegative (4 * fraction - 1))
    (show 0 ≤ (4 * fraction - 5) ^ 2 + 2 by
      have lower := squareNonnegative (4 * fraction - 5)
      grind)
  have identity : 27 - 256 * fraction * (1 - fraction) ^ 3 =
      (4 * fraction - 1) ^ 2 * ((4 * fraction - 5) ^ 2 + 2) := by
    grind
  grind

theorem periodic_reduced_radius_gate (residual defect bend radius : Rat)
    (bendPositive : 0 < bend)
    (gate : residual + defect * radius + bend * radius ^ 2 / 2 < radius) :
    2 * bend * residual < (1 - defect) ^ 2 := by
  have scaled := Rat.mul_lt_mul_of_pos_left gate
    (show 0 < 2 * bend by grind)
  have square : 0 ≤ (1 - defect - bend * radius) ^ 2 := by
    by_cases nonnegative : 0 ≤ 1 - defect - bend * radius
    · exact Rat.pow_nonneg nonnegative
    · have opposite := Rat.pow_nonneg (n := 2)
        (show 0 ≤ -(1 - defect - bend * radius) by grind)
      grind
  have identity : (1 - defect) ^ 2 -
      2 * bend * ((1 - defect) * radius - bend * radius ^ 2 / 2) =
      (1 - defect - bend * radius) ^ 2 := by
    grind
  grind

theorem periodic_projection_budget_split (timeFraction : Rat) (withinBudget : timeFraction ≤ 1) :
    timeFraction * (1 - timeFraction)^2 ≤ 4 / 27 := by
  have squareNonnegative : 0 ≤ (timeFraction - 1 / 3)^2 := by
    by_cases h : 0 ≤ timeFraction - 1 / 3
    · exact Rat.pow_nonneg h
    · have opposite := Rat.pow_nonneg (n := 2) (show 0 ≤ -(timeFraction - 1 / 3) by grind)
      grind
  have product := Rat.mul_nonneg squareNonnegative
    (show 0 ≤ 4 / 3 - timeFraction by grind)
  have identity :
    4 / 27 - timeFraction * (1 - timeFraction)^2 =
      (timeFraction - 1 / 3)^2 * (4 / 3 - timeFraction) := by
    grind
  grind

theorem periodic_weighted_phase_gate
    (amplitude delta timeBudget spaceBudget timeTail spaceTail : Rat)
    (amplitudePositive : 0 < amplitude) (deltaPositive : 0 < delta)
    (scaledBudget : delta * amplitude ≤ 1 / 16)
    (jointBudget : timeBudget + spaceBudget ≤ delta)
    (timeBound : timeTail ≤ timeBudget) (spaceBound : spaceTail ≤ spaceBudget) :
    timeTail + spaceTail ≤ delta ∧ 0 < 4 * delta * (2 * amplitude) ∧
      4 * delta * (2 * amplitude) ≤ 1 / 2 := by
  have product := Rat.mul_pos deltaPositive amplitudePositive
  exact ⟨by grind, by grind, by grind⟩

theorem periodic_bilinear_mode_transfer {Scale X : Type _} [Mul Scale]
    (scale : Scale → X → X) (shift : X → X) (combine : X → X → X)
    (covariant : ∀ v w, shift (combine v w) = combine (shift v) (shift w))
    (homogeneous : ∀ a b v w, combine (scale a v) (scale b w) = scale (a * b) (combine v w))
    {a b : Scale} {v w : X}
    (left : shift v = scale a v) (right : shift w = scale b w) :
    shift (combine v w) = scale (a * b) (combine v w) := by
  rw [covariant, left, right, homogeneous]

theorem periodic_swirl_barrier_positive (bound drift rate factor : Rat)
    (boundNonnegative : 0 ≤ bound) (driftLower : -bound ≤ drift)
    (rateLower : 2 * bound + 1 ≤ rate) (factorPositive : 0 < factor)
    (region : 0 < drift ∨ 1 ≤ factor) :
    0 < drift + (rate + drift) * factor := by
  have coefficient : bound + 1 ≤ rate + drift := by grind
  have coefficientPositive : 0 < rate + drift := by grind
  rcases region with positiveDrift | factorLower
  · have product := Rat.mul_pos coefficientPositive factorPositive
    grind
  · have product := Rat.mul_le_mul_of_nonneg_left factorLower (Rat.le_of_lt coefficientPositive)
    grind

theorem periodic_rational_rotation_no_return (real imag : Nat → Int)
    (realBase : real 0 = 1) (imagBase : imag 0 = 0)
    (realStep : ∀ n, real (n + 1) = 3 * real n - 4 * imag n)
    (imagStep : ∀ n, imag (n + 1) = 4 * real n + 3 * imag n)
    {n : Nat} (positive : 0 < n) : ¬ (real n = 5 ^ n ∧ imag n = 0) := by
  have preservesResidue : ∀ k, (real k + 2 * imag k) % 5 = 1 := by
    intro k
    induction k with
    | zero => rw [realBase, imagBase]; decide
    | succ k ih =>
      rw [realStep, imagStep]
      omega
  rintro ⟨returnsReal, returnsImag⟩
  have residue := preservesResidue n
  rw [returnsReal, returnsImag] at residue
  cases n with
  | zero => omega
  | succ k =>
    rw [Int.pow_succ] at residue
    omega

theorem periodic_centered_residual {Z : Type _} [Abelian Z]
    (mean : AddMap Z Z) (quadratic : Z → Z → Z) (a w : Z)
    (addLeft : ∀ x y z, quadratic (x + y) z = quadratic x z + quadratic y z)
    (addRight : ∀ x y z, quadratic x (y + z) = quadratic x y + quadratic x z)
    (fixMean : mean a = a) (centered : mean w = 0)
    (fixStationary : mean (quadratic a a) = quadratic a a)
    (leftCentered : mean (quadratic a w) = 0)
    (rightCentered : mean (quadratic w a) = 0) :
    mean (a + w + quadratic (a + w) (a + w)) =
      a + quadratic a a + mean (quadratic w w) := by
  rw [periodic_projected_quadratic mean quadratic a w addLeft addRight centered]
  simp only [mean.map_add, fixMean, fixStationary, leftCentered, rightCentered, Abelian.zero_add]

theorem periodic_low_harmonic_lower (fluctuation low tail lower : Rat)
    (lowerBound : lower ≤ fluctuation)
    (decomposition : fluctuation ≤ low + tail)
    (tailBound : tail ≤ fluctuation / 2) :
    lower / 2 ≤ low := by
  grind

theorem periodic_enstrophy_ratio_gate (t : Rat) (nonnegative : 0 ≤ t) :
    18 * t ^ 2 < 5 * (1 + t ^ 2) * (1 + t) ∧
      (∀ angular : Rat, 5 ≤ angular →
        (angular + 3) * t ^ 2 < (1 + t ^ 2) * (angular + t)) := by
  have square (x : Rat) : 0 ≤ x ^ 2 := by
    by_cases h : 0 ≤ x
    · exact Rat.pow_nonneg h
    · have opposite := Rat.pow_nonneg (n := 2) (show 0 ≤ -x by grind)
      grind
  have first := Rat.mul_nonneg (show 0 ≤ 5 * t by grind) (square (t - 3 / 2))
  have second := Rat.mul_nonneg (show (0 : Rat) ≤ 2 by decide) (square (t - 25 / 16))
  have identity : 5 * (1 + t ^ 2) * (1 + t) - 18 * t ^ 2 =
      5 * t * (t - 3 / 2) ^ 2 + 2 * (t - 25 / 16) ^ 2 + 15 / 128 := by
    grind
  have reflectionIdentity : (1 + t ^ 2) * (5 + t) - 8 * t ^ 2 =
      (t + 1) * ((t - 2) ^ 2 + 1) := by grind
  have reflectionPositive :=
    Rat.mul_pos (show 0 < t + 1 by grind)
      (show 0 < (t - 2) ^ 2 + 1 by have h := square (t - 2); grind)
  constructor
  · grind
  · intro angular lower
    have difference : (1 + t ^ 2) * (angular + t) - (angular + 3) * t ^ 2 =
        ((1 + t ^ 2) * (5 + t) - 8 * t ^ 2) + (angular - 5) := by grind
    grind

theorem periodic_tree_radius (s M eta R : Rat)
    (nonnegS : 0 ≤ s) (positiveGap : 0 < eta)
    (gapBound : 4 * M * s + eta ^ 2 ≤ 1)
    (radius : R * (1 + eta) = 2 * s) :
    M * R ^ 2 ≤ R - s ∧ 2 * M * R < 1 := by
  have positive : 0 < 1 + eta := by grind
  have positiveSquare : 0 < (1 + eta) ^ 2 := by
    simpa [Rat.pow_succ, Rat.pow_zero, Rat.one_mul] using Rat.mul_pos positive positive
  have square : (R * (1 + eta)) * (R * (1 + eta)) = (2 * s) * (2 * s) := by rw [radius]
  have scaledRadius := congrArg (fun a : Rat => a * (1 + eta)) radius
  have scaledRate := congrArg (fun a : Rat => 2 * M * a) radius
  have scaled : (R - s - M * R ^ 2) * (1 + eta) ^ 2 =
      s * (1 - eta ^ 2 - 4 * M * s) := by
    simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
    grind
  have nonneg : 0 ≤ s * (1 - eta ^ 2 - 4 * M * s) :=
    Rat.mul_nonneg nonnegS (by grind)
  have room : 0 ≤ R - s - M * R ^ 2 := by
    apply Rat.le_of_mul_le_mul_right _ positiveSquare
    rw [Rat.zero_mul, scaled]
    exact nonneg
  have etaSquare : 0 ≤ eta ^ 2 := by
    have weak := Rat.le_of_lt positiveGap
    simpa [Rat.pow_succ, Rat.pow_zero, Rat.one_mul] using Rat.mul_nonneg weak weak
  have rate : (2 * M * R) * (1 + eta) < 1 * (1 + eta) := by grind
  exact ⟨by grind, Rat.lt_of_mul_lt_mul_right rate (Rat.le_of_lt positive)⟩

theorem periodic_joint_radial_gate (linearRead exactRead error : Rat)
    (margin : error < linearRead) (lower : -error ≤ exactRead - linearRead) :
    0 < exactRead := by
  grind

theorem periodic_chart_caps :
    (1/4 + 4 * (1/128) : Rat) < 1/2 ∧
    (2 * (1/256 + (1/128)/4 + 2 * (1/128)^2) : Rat) ≤ 1/64 ∧
    (4 * 4 * (1/64) : Rat) = 1/4 := by
  decide +kernel

theorem leray_kernel_constant :
    (3 : Rat) < (7 / 4) ^ 2 ∧ (10 + 6 * (7 / 4) : Rat) ^ 2 < 144 * 3 := by
  decide +kernel

theorem curl_residual_writeback {Pressure Velocity Curl : Type _}
    [Abelian Pressure] [Abelian Velocity] [Abelian Curl]
    (complex : TwoStep Pressure Velocity Curl) (curlLift : Curl → Velocity)
    (gradientLift : Velocity → Pressure) (residual : Velocity)
    (lift_curl : complex.down (curlLift (complex.down residual)) = complex.down residual)
    (lift_gradient : ∀ v, complex.down v = 0 → complex.up (gradientLift v) = v) :
    residual + complex.up (gradientLift (curlLift (complex.down residual) + -residual)) =
      curlLift (complex.down residual) := by
  let force := curlLift (complex.down residual)
  have closed : complex.down (force + -residual) = 0 := by
    rw [complex.down.map_add, complex.down.map_neg, lift_curl, Abelian.add_neg]
  change residual + complex.up (gradientLift (force + -residual)) = force
  rw [lift_gradient _ closed, ← Abelian.assoc, Abelian.comm residual force,
    Abelian.assoc, Abelian.add_neg, Abelian.add_zero]

theorem successive_differences_telescope {A : Type _} [Abelian A]
    (state : Nat → A) (start count : Nat) :
    finiteSum (fun n => state (n + 1) + -state n) (List.range' start count) =
      state (start + count) + -state start := by
  induction count generalizing start with
  | zero => simp [finiteSum]
  | succ count ih =>
    rw [List.range'_succ, finiteSum, ih]
    have endpoint : start + 1 + count = start + (count + 1) := by omega
    rw [endpoint]
    calc
      _ = (state (start + (count + 1)) + -state start) +
                (state (start + 1) + -state (start + 1)) := by ac_rfl
      _ = _ := by rw [Abelian.add_neg, Abelian.add_zero]

theorem profile_geometric_identity (rate bound : Rat) (start count : Nat) :
    (1 - rate) * finiteSum (fun k => bound * rate ^ (k + 1)) (List.range' start count) =
      bound * rate ^ (start + 1) - bound * rate ^ (start + count + 1) := by
  induction count generalizing start with
  | zero =>
    change (1 - rate) * 0 = bound * rate ^ (start + 1) - bound * rate ^ (start + 1)
    rw [Rat.mul_zero, Rat.sub_self]
  | succ count ih =>
    rw [List.range'_succ, finiteSum]
    have tail := ih (start + 1)
    have last : start + 1 + count + 1 = start + (count + 1) + 1 := by omega
    rw [last] at tail
    calc
      _ = (1 - rate) * (bound * rate ^ (start + 1)) +
          (1 - rate) * finiteSum (fun k => bound * rate ^ (k + 1))
            (List.range' (start + 1) count) := by grind
      _ = _ := by rw [tail, Rat.pow_succ rate (start + 1)]; grind

theorem periodic_fluctuation_absorbs (amplitude rate : Rat) (nonnegative : 0 ≤ amplitude)
    (contracts : rate < 1) (estimate : amplitude ≤ rate * amplitude) : amplitude = 0 := by
  by_cases zero : amplitude = 0
  · exact zero
  · have positive : 0 < amplitude := by grind
    have strict := Rat.mul_lt_mul_of_pos_right contracts positive
    grind

theorem periodic_rotating_frame_period {X : Type _}
    (flow : Rat → X) (rotate : Rat → X → X) (period angularSpeed : Rat)
    (compose : ∀ a b x, rotate a (rotate b x) = rotate (a + b) x)
    (seam : ∀ s, flow (s + period) = rotate (angularSpeed * period) (flow s)) (s : Rat) :
    rotate (-angularSpeed * (s + period)) (flow (s + period)) =
      rotate (-angularSpeed * s) (flow s) := by
  have angle : -angularSpeed * (s + period) + angularSpeed * period = -angularSpeed * s := by
    grind
  rw [seam, compose, angle]

theorem periodic_rotation_gap_budget (gap root logValue heat rotation : Rat)
    (gapNonneg : 0 ≤ gap) (gapBound : gap ≤ root)
    (heatNonneg : 0 ≤ heat) (rotationNonneg : 0 ≤ rotation)
    (logBound : gap * logValue ≤ 2 * (root - gap)) :
    gap * (4 * heat + 2 * rotation * (1 + logValue)) ≤ 4 * (heat + rotation) * root := by
  have scaledLog := Rat.mul_le_mul_of_nonneg_left logBound
    (show 0 ≤ 2 * rotation by grind)
  have scaledHeat := Rat.mul_le_mul_of_nonneg_left gapBound
    (show 0 ≤ 4 * heat by grind)
  have rotationTerm := Rat.mul_nonneg rotationNonneg gapNonneg
  grind

theorem periodic_head_pressure_cancel
    (head radial drift speedSq viscosity curlSq meanForce positionForce forceDivergence : Rat)
    (headEq : head =
      drift / 2 - speedSq / 2 - viscosity * curlSq + meanForce - viscosity * forceDivergence)
    (radialEq : radial = speedSq - drift + positionForce) :
    head + radial / 2 =
      -viscosity * curlSq + meanForce + positionForce / 2 - viscosity * forceDivergence := by
  grind

theorem periodic_diffusion_ball_reach
    (linearDistance driftDistance speed step radius : Rat)
    (linearInside : linearDistance ≤ radius / 2)
    (driftBound : driftDistance ≤ speed * step)
    (stepBound : speed * step ≤ radius / 2) :
    linearDistance + driftDistance ≤ radius := by
  grind

theorem periodic_pressure_cell_floor
    (pressure correction viscosity enstrophy cellMass curlSq : Rat)
    (viscosityNonnegative : 0 ≤ viscosity)
    (balance : pressure = viscosity * enstrophy)
    (correctionMean : correction = 0)
    (cellBound : cellMass * curlSq ≤ enstrophy) :
    viscosity * (cellMass * curlSq) ≤ pressure - correction := by
  have lower := Rat.mul_le_mul_of_nonneg_left cellBound viscosityNonnegative
  grind

theorem pressure_outer_weight_ratio
    (weight threshold size : Rat) (weightNonnegative : 0 ≤ weight)
    (outside : threshold ≤ size) :
    (2 + 3 * weight * size / 4) * (2 + weight * threshold) ≤
      (2 + 3 * weight * threshold / 4) * (2 + weight * size) := by
  have nonnegative := Rat.mul_nonneg weightNonnegative (show 0 ≤ size - threshold by grind)
  grind

theorem pressure_inner_weight_ratio
    (overlap weightedSize weightedDrift : Rat)
    (overlapNonnegative : 0 ≤ overlap) (overlapUpper : overlap ≤ 1)
    (sizeNonnegative : 0 ≤ weightedSize) (driftBound : 2 * weightedDrift ≤ overlap / 2) :
    2 * (1 - overlap) + weightedSize / 2 + 2 * weightedDrift ≤
      (1 - overlap / 2) * (2 + weightedSize) := by
  have nonnegative := Rat.mul_nonneg (show 0 ≤ 1 - overlap by grind) sizeNonnegative
  grind

theorem periodic_pressure_scalar_readback
    (base perturbation margin coefficient defect : Rat)
    (positiveMargin : 0 < margin) (baseFloor : 2 * margin ≤ base)
    (errorLower : -margin ≤ perturbation)
    (balance : defect = (base + perturbation) * coefficient) :
    margin ≤ base + perturbation ∧ (defect = 0 ↔ coefficient = 0) := by
  have floor : margin ≤ base + perturbation := by grind
  have nonzero : base + perturbation ≠ 0 := by grind
  refine ⟨floor, ?_⟩
  rw [balance]
  constructor
  · intro zero
    exact (Rat.mul_eq_zero.mp zero).resolve_left nonzero
  · intro zero
    simp [zero]

theorem periodic_pressure_phase_balance
    (head pressureHead pressureTime pressureDiffusion pressureDrift curlLoss gradientLoss response : Rat)
    (headEquation : head = pressureTime - curlLoss + response)
    (pressureEquation : pressureHead = pressureTime - pressureDiffusion + pressureDrift)
    (lossEquation : gradientLoss = curlLoss - pressureDiffusion) :
    response = head - pressureHead + gradientLoss + pressureDrift := by
  grind

theorem periodic_pressure_phase_projection {Phase Residual : Type _}
    (lift : (Phase → Rat) → Residual) (observe : Residual → Phase → Rat) (gain : Phase → Rat)
    (gainPositive : ∀ s, 0 < gain s)
    (observed : ∀ coefficient s, observe (lift coefficient) s = gain s * coefficient s) :
    let read := fun residual s => observe residual s / gain s
    (∀ coefficient, read (lift coefficient) = coefficient) ∧
      (∀ residual, lift (read (lift (read residual))) = lift (read residual)) := by
  let read := fun residual s => observe residual s / gain s
  have recover (coefficient : Phase → Rat) : read (lift coefficient) = coefficient := by
    funext s
    dsimp [read]
    rw [observed, Rat.mul_comm (gain s) (coefficient s), Rat.mul_div_cancel (Rat.ne_of_gt (gainPositive s))]
  exact ⟨recover, fun residual => congrArg lift (recover (read residual))⟩

theorem periodic_pressure_phase_interval_budget
    (amplitude observation error modulus width gain : Rat)
    (widthPositive : 0 < width) (gainPositive : 0 < gain)
    (weightedBound : (amplitude - modulus) * (width * gain) ≤ observation + error) :
    amplitude ≤ (observation + error) / (width * gain) + modulus := by
  have scalePositive := Rat.mul_pos widthPositive gainPositive
  have scaled : (amplitude - modulus) * (width * gain) ≤
      ((observation + error) / (width * gain)) * (width * gain) := by
    simpa only [Rat.div_mul_cancel (Rat.ne_of_gt scalePositive)] using weightedBound
  have divided := Rat.le_of_mul_le_mul_right scaled scalePositive
  grind

theorem periodic_head_barrier_budget (error loss barrier penalty inside outside : Rat)
    (smallError : error < penalty) (balance : loss = (1 + barrier) * penalty)
    (insideUpper : inside ≤ error - loss + penalty * barrier)
    (outsideUpper : outside ≤ error - penalty) :
    inside < 0 ∧ outside < 0 := by
  grind

theorem periodic_phase_gap_bound (amplitude fluctuation loss scale : Rat)
    (positiveScale : 0 < scale)
    (dissipation : fluctuation < amplitude → loss ≤ scale * fluctuation) :
    min amplitude (loss / scale) ≤ fluctuation := by
  by_cases below : fluctuation < amplitude
  · have scaled : loss / scale ≤ fluctuation := by
      apply Rat.le_of_mul_le_mul_right _ positiveScale
      rw [Rat.div_mul_cancel (Rat.ne_of_gt positiveScale), Rat.mul_comm fluctuation scale]
      exact dissipation below
    rw [Rat.min_def]
    split <;> grind
  · rw [Rat.min_def]
    split <;> grind

theorem gaussian_reference_amplitude_read (root trial energy pairing viscosity : Rat)
    (chosen : root * pairing = -(2 * viscosity * energy)) :
    root * (2 * viscosity * trial * energy + trial ^ 2 * pairing) =
      2 * viscosity * energy * trial * (root - trial) := by
  have scaled := congrArg (fun value => trial * trial * value) chosen
  simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
  grind

theorem periodic_second_harmonic_cosine (amplitude radius sineProduct cosineProduct : Rat) :
    (amplitude * radius / 2) ^ 2 * cosineProduct / 2 -
      (amplitude * radius) ^ 2 * sineProduct / 2 =
        amplitude ^ 2 * radius ^ 2 * (cosineProduct - 4 * sineProduct) / 8 := by
  simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
  grind

theorem periodic_gaussian_moment_caps :
    (3 : Rat) ≤ (7 / 4) ^ 2 ∧ (16 : Rat) ≤ 3 * (7 / 3) ^ 2 ∧
    (7 / 4 : Rat) * (19 / 8) + 891 / 64 ≤ 19 ∧
    (7 / 4 : Rat) * (161 / 24) + 2 * (2807 / 64) ≤ 100 ∧
    (4 : Rat) * (259 / 48) ≤ 22 := by
  decide +kernel

theorem periodic_phase_border_coordinates {E Phase : Type _} [Abelian E] [Abelian Phase]
    (linear : AddMap E E) (insert : AddMap Phase E) (read : AddMap E Phase)
    (base target : E) (parameters correction phase : Phase)
    (nullColumns : ∀ p, linear (insert p) = 0)
    (linearMatch : linear base + -(insert parameters) = target)
    (phaseMatch : read (insert correction) = phase + -(read base)) :
    linear (base + insert correction) + -(insert parameters) = target ∧
      read (base + insert correction) = phase := by
  constructor
  · rw [linear.map_add, nullColumns, Abelian.add_zero, linearMatch]
  · calc
      read (base + insert correction) = read base + (phase + -(read base)) := by
        rw [read.map_add, phaseMatch]
      _ = phase + (read base + -(read base)) := by
        rw [← Abelian.assoc, Abelian.comm (read base) phase, Abelian.assoc]
      _ = phase := by rw [Abelian.add_neg, Abelian.add_zero]

def cubicHarmonicIndices (degreeHalf : Nat) : List (Nat × Nat) :=
  (List.range (degreeHalf / 3 + 1)).filterMap fun b =>
    let remainder := degreeHalf - 3 * b
    if remainder % 2 = 0 then some (remainder / 2, b) else none

theorem cubic_harmonic_indices_complete (degreeHalf a b : Nat) :
    (a, b) ∈ cubicHarmonicIndices degreeHalf ↔ 2 * a + 3 * b = degreeHalf := by
  constructor
  · intro mem
    obtain ⟨k, within, keeps⟩ := List.mem_filterMap.mp mem
    have bound := List.mem_range.mp within
    dsimp at keeps
    split at keeps
    · rename_i even
      have pair := Option.some.inj keeps
      have first := congrArg Prod.fst pair
      have second := congrArg Prod.snd pair
      dsimp at first second
      omega
    · contradiction
  · intro degree
    apply List.mem_filterMap.mpr
    refine ⟨b, List.mem_range.mpr (by omega), ?_⟩
    have remainder : degreeHalf - 3 * b = 2 * a := by omega
    simp [remainder]

theorem harmonic_projection_coeff_cancel (coefficient degree index : Rat)
    (nonzero : 2 * (index + 1) * (2 * degree - 2 * index - 1) ≠ 0) :
    coefficient + (-coefficient / (2 * (index + 1) * (2 * degree - 2 * index - 1))) *
      (2 * (index + 1) * (2 * degree - 2 * index - 1)) = 0 := by
  rw [Rat.div_mul_cancel nonzero]
  grind

theorem poloidal_harmonic_product_coefficients (degree : Rat) :
    2 * (degree * (degree + 1)) - (2 * degree) * (2 * degree + 1) = -2 * degree ^ 2 ∧
      2 * degree ^ 2 - degree * (degree + 1) = degree * (degree - 1) := by
  constructor <;> grind

theorem toroidal_harmonic_top_coefficient (degree square radiusDerivative : Rat) :
    degree ^ 2 * (2 * square + radiusDerivative) -
      degree * (degree + 1) * radiusDerivative =
      degree * (2 * degree * square - radiusDerivative) := by
  grind

theorem even_harmonic_root_order_preserved (half current previous auxiliaryChange : Int)
    (halfNonnegative : 0 ≤ half)
    (currentBound : 0 ≤ current ∧ current ≤ 2 * half)
    (previousBound : 0 ≤ previous ∧ previous ≤ 2 * half)
    (balance : (2 * half + 1) * auxiliaryChange =
      (2 * half - 1) * (current - previous)) :
    current = previous := by
  let delta := current - previous
  let quotient := half * delta - (half + 1) * auxiliaryChange
  have factor : delta = (2 * half + 1) * quotient := by
    change (2 * half + 1) * auxiliaryChange = (2 * half - 1) * delta at balance
    calc
      delta = (2 * half + 1) * (half * delta) -
          (half + 1) * ((2 * half - 1) * delta) := by grind
      _ = (2 * half + 1) * (half * delta) -
          (half + 1) * ((2 * half + 1) * auxiliaryChange) := by rw [← balance]
      _ = (2 * half + 1) * quotient := by dsimp [quotient]; grind
  have bounds : -(2 * half + 1) < delta ∧ delta < 2 * half + 1 := by
    dsimp [delta]
    omega
  have nonnegative : 0 ≤ 2 * half + 1 := by omega
  by_cases positive : 1 ≤ quotient
  · have outside := Int.mul_le_mul_of_nonneg_left positive nonnegative
    rw [Int.mul_one, ← factor] at outside
    omega
  · by_cases negative : quotient ≤ -1
    · have outside := Int.mul_le_mul_of_nonneg_left negative nonnegative
      rw [← factor, Int.mul_neg_one] at outside
      omega
    · have zero : quotient = 0 := by omega
      rw [zero, Int.mul_zero] at factor
      dsimp [delta] at factor
      omega

theorem cubic_poloidal_residual_polynomial (x : Rat) :
    5 * (-88 + 64 * x - 8 * x ^ 2) - 8 * (5 - 2 * x) * (2 * x - 11) =
      8 * x * (8 - x) := by
  grind

theorem gaussian_period_square_balance
    (viscosity enstrophy radialSquare headSquare cross joinedSquare work : Rat)
    (expanded : joinedSquare = headSquare + 2 * cross + radialSquare)
    (balance : 4 * viscosity ^ 2 * enstrophy + radialSquare + 2 * cross =
      4 * viscosity * work) :
    4 * viscosity ^ 2 * enstrophy + joinedSquare = headSquare + 4 * viscosity * work := by
  grind

theorem gaussian_period_energy_gate
    (viscosity gradient kinetic cross work kineticLower workUpper lossUpper : Rat)
    (positive : 0 < viscosity) (gradientNonnegative : 0 ≤ gradient)
    (balance : 2 * viscosity * viscosity * gradient + viscosity * kinetic + cross =
      2 * viscosity * work)
    (kineticBound : kineticLower ≤ kinetic) (workBound : work ≤ workUpper)
    (lossBound : -lossUpper ≤ cross) :
    viscosity * kineticLower ≤ 2 * viscosity * workUpper + lossUpper := by
  have nonnegative := Rat.le_of_lt positive
  have twiceNonnegative : 0 ≤ 2 * viscosity := Rat.mul_nonneg (by decide) nonnegative
  have dissipates :=
    Rat.mul_nonneg (Rat.mul_nonneg twiceNonnegative nonnegative) gradientNonnegative
  have kineticCompare := Rat.mul_le_mul_of_nonneg_left kineticBound nonnegative
  have workCompare := Rat.mul_le_mul_of_nonneg_left workBound twiceNonnegative
  grind

theorem period_pulse_contraction_gate
    (radius center linear quadratic distance : Rat)
    (centerBound : center ≤ radius / 4) (linearBound : linear ≤ 1 / 4)
    (quadraticBound : quadratic ≤ 1 / 4) (distanceNonnegative : 0 ≤ distance)
    (distanceBound : distance ≤ radius) :
    linear + quadratic ≤ 1 / 2 ∧ center + (linear + quadratic) * distance ≤ radius := by
  have sumBound : linear + quadratic ≤ 1 / 2 := by grind
  have first := Rat.mul_le_mul_of_nonneg_right sumBound distanceNonnegative
  have halfNonnegative : (0 : Rat) ≤ 1 / 2 := by decide +kernel
  have second := Rat.mul_le_mul_of_nonneg_left distanceBound halfNonnegative
  exact ⟨sumBound, by grind⟩

theorem parabolic_ratio_chart (time radius ratio phase coordinate : Rat) :
    time + (1 - ratio ^ 2) * radius ^ 2 + (ratio * radius) ^ 2 * phase =
      time + radius ^ 2 * (1 - ratio ^ 2 + ratio ^ 2 * phase) ∧
    (ratio * radius) * coordinate = radius * (ratio * coordinate) := by
  simp only [Rat.pow_succ, Rat.pow_zero, Rat.one_mul]
  constructor <;> grind

theorem periodic_sample_locked {Z V : Type _} [Abelian Z] [Abelian V]
    (read : AddMap Z V) (project : Z → Z)
    (preserves : ∀ z, read (project z) = read z)
    (center tail : Z) (tailProjection : project tail = 0) :
    read (center + tail) = read center := by
  have tailRead : read tail = 0 := by rw [← preserves tail, tailProjection, read.map_zero]
  rw [read.map_add, tailRead, Abelian.add_zero]

theorem scaled_peak_lower (reference actual error : Rat)
    (approximation : reference - error ≤ actual) (small : error ≤ reference / 2) :
    reference / 2 ≤ actual := by
  grind

theorem affine_chart_compose {X Y Z : Type _} [Abelian X] [Abelian Y] [Abelian Z]
    (first : AddMap X Y) (second : AddMap Y Z) (state : X) (a : Y) (b : Z) :
    second (first state + a) + b = second (first state) + (second a + b) := by
  rw [second.map_add, Abelian.assoc]

theorem observed_rate_telescope {Rate TestValue : Type _} [Abelian Rate] [Abelian TestValue]
    (rate : Nat → Rate) (observe : AddMap Rate TestValue) (start count : Nat) :
    finiteSum (fun n => observe (rate (n + 1) + -rate n)) (List.range' start count) =
      observe (rate (start + count) + -rate start) := by
  rw [← finiteSum_map, successive_differences_telescope]

theorem affine_product_delta (left right leftStep rightStep : Rat) :
    (left + leftStep) * (right + rightStep) - left * right =
      left * rightStep + right * leftStep + leftStep * rightStep := by
  grind

theorem periodic_seam_covariance {X Y : Type _} [Abelian X] [Abelian Y]
    (transport : AddMap X Y) (heat seam : AddMap X X) (targetHeat targetSeam : AddMap Y Y)
    (heatLaw : ∀ x, transport (heat x) = targetHeat (transport x))
    (seamLaw : ∀ x, transport (seam x) = targetSeam (transport x))
    (initial source : X) (seamMatch : initial = seam (heat initial + source)) :
    transport initial = targetSeam (targetHeat (transport initial) + transport source) := by
  calc
    transport initial = transport (seam (heat initial + source)) :=
      congrArg (fun x => transport x) seamMatch
    _ = _ := by rw [seamLaw, transport.map_add, heatLaw]

theorem periodic_frame_readback {X Y : Type _}
    (current next : X → Y) (movePoint : X → X) (moveValue undoValue : Y → Y)
    (seamMatch : ∀ p, next (movePoint p) = moveValue (current p))
    (returns : ∀ y, undoValue (moveValue y) = y) :
    (fun p => undoValue (next (movePoint p))) = current := by
  funext p
  rw [seamMatch, returns]

end GAlgebra
