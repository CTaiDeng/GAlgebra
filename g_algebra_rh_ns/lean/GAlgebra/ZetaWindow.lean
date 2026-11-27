import GAlgebra.ArithmeticEnclosures

set_option autoImplicit false
namespace GAlgebra

structure RationalComplex where
  re : Rat
  im : Rat

namespace RationalComplex

private def add (z w : RationalComplex) : RationalComplex :=
  ⟨z.re + w.re, z.im + w.im⟩

private def mul (z w : RationalComplex) : RationalComplex :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

private def scale (z : RationalComplex) (scale : Rat) : RationalComplex :=
  ⟨z.re * scale, z.im * scale⟩

private def addReal (z : RationalComplex) (constant : Rat) : RationalComplex :=
  ⟨z.re + constant, z.im⟩

def roundedCoordinate (units : Rat) (x : Rat) : Rat :=
  ((x * units).floor : Rat) / units

theorem rounded_coordinate_error (units x : Rat) (positive : 0 < units) :
    0 ≤ x - roundedCoordinate units x ∧ x - roundedCoordinate units x < 1 / units := by
  have rounded : roundedCoordinate units x * units = ((x * units).floor : Rat) :=
    Rat.div_mul_cancel (Rat.ne_of_gt positive)
  have difference : (x - roundedCoordinate units x) * units =
      x * units - ((x * units).floor : Rat) := by
    rw [Rat.sub_eq_add_neg, Rat.add_mul, Rat.neg_mul, rounded, Rat.sub_eq_add_neg]
  have lower := Rat.floor_le (x * units)
  have upper := Rat.lt_floor_add_one (x * units)
  simp only [Rat.intCast_add, Rat.intCast_one] at upper
  constructor
  · refine Rat.le_of_mul_le_mul_right ?_ positive
    rw [difference, Rat.zero_mul]
    grind
  · apply (Rat.lt_div_iff positive).mpr
    rw [difference]
    grind

private def gridProduct (p q : Int × Int) (divisor : Int) : Int × Int :=
  ((p.1 * q.1 - p.2 * q.2) / divisor, (p.1 * q.2 + p.2 * q.1) / divisor)

private def expGrid (units : Int) (seriesDivisors : List Int) (squaringSteps : List Nat)
    (numerator : Int × Int) : Int × Int :=
  let one : Int × Int := (units, 0)
  let (_, total) := seriesDivisors.foldl (fun (term, total) divisor =>
    let next := gridProduct term numerator divisor
    (next, (total.1 + next.1, total.2 + next.2))) (one, one)
  squaringSteps.foldl (fun value _ => gridProduct value value units) total

private def logGrid (units : Rat) (terms n : Nat) (positive : 0 < n) : Int :=
  (((naturalLogSequence n positive).bounds terms).lower * units).floor

private def zetaValue (units squarings degree : Nat) (cutoff : Rat)
    (logs : List Int) (tailLog : Int) (s : RationalComplex) : RationalComplex :=
  -- All scaled exponents at this vertex share a denominator.
  let realFactor := -s.re.num * (s.im.den : Int)
  let imaginaryFactor := -s.im.num * (s.re.den : Int)
  let denominator : Int := (s.re.den * s.im.den * units * 2 ^ squarings : Nat)
  let divisors := (List.range' 1 degree).map (fun (k : Nat) => denominator * (k : Int))
  let squaringSteps := List.range squarings
  let sample := fun logN =>
    expGrid units divisors squaringSteps (realFactor * logN, imaginaryFactor * logN)
  let fromGrid := fun (value : Int × Int) =>
    (⟨(value.1 : Rat) / (units : Rat), (value.2 : Rat) / (units : Rat)⟩ : RationalComplex)
  let partialGrid := logs.foldl (fun sum logN =>
    let term := sample logN
    (sum.1 + term.1, sum.2 + term.2)) (0, 0)
  let partialSum := fromGrid partialGrid
  let falling := (s.mul (s.addReal 1)).mul (s.addReal 2)
  let correction := ((s.scale (1 / (12 * cutoff))).addReal (1 / 2)).add
    (falling.scale (-1 / (720 * cutoff ^ 3)))
  let endTerm := fromGrid (sample tailLog)
  ((s.addReal (-1)).mul (partialSum.add (correction.mul endTerm))).add (endTerm.scale cutoff)

def determinant (p q : RationalComplex) : Rat :=
  p.re * q.im - q.re * p.im

theorem crossing_coordinate (p q : RationalComplex) (nonhorizontal : q.im ≠ p.im) :
    let parameter := -p.im / (q.im - p.im)
    ((1 - parameter) * p.re + parameter * q.re) * (q.im - p.im) = determinant p q := by
  dsimp
  let difference := q.im - p.im
  let parameter := -p.im / difference
  have nonzero : difference ≠ 0 := by dsimp [difference]; grind
  have hits : parameter * difference = -p.im := Rat.div_mul_cancel nonzero
  change ((1 - parameter) * p.re + parameter * q.re) * difference = determinant p q
  calc
    _ = p.re * difference + (q.re - p.re) * (parameter * difference) := by grind
    _ = _ := by rw [hits]; dsimp [difference, determinant]; grind

def Separated (margin : Rat) (p q : RationalComplex) : Prop :=
  (margin < p.re ∧ margin < q.re) ∨ (p.re < -margin ∧ q.re < -margin) ∨
  (margin < p.im ∧ margin < q.im) ∨ (p.im < -margin ∧ q.im < -margin)

theorem segment_coordinate_above (a b parameter threshold : Rat)
    (first : threshold < a) (second : threshold < b)
    (nonnegative : 0 ≤ parameter) (at_most_one : parameter ≤ 1) :
    threshold < (1 - parameter) * a + parameter * b := by
  by_cases zero : parameter = 0
  · grind
  · have term₁ := Rat.mul_nonneg (show 0 ≤ 1 - parameter by grind)
      (show 0 ≤ a - threshold by grind)
    have term₂ := Rat.mul_pos (show 0 < parameter by grind) (show 0 < b - threshold by grind)
    grind

instance (margin : Rat) (p q : RationalComplex) : Decidable (Separated margin p q) := by
  unfold Separated
  infer_instance

private def crossing (p q : RationalComplex) : Int :=
  if p.im ≤ 0 ∧ 0 < q.im ∧ 0 < determinant p q then 1
  else if q.im ≤ 0 ∧ 0 < p.im ∧ determinant p q < 0 then -1
  else 0

theorem crossing_reverse (p q : RationalComplex) : crossing q p = -crossing p q := by
  have opposite : determinant q p = -determinant p q := by unfold determinant; grind
  unfold crossing
  grind

structure ContourError where
  truncation : Rat
  rounding : Rat
  curvature : Rat

def ContourError.margin (error : ContourError) (width : Rat) : Rat :=
  error.truncation + error.rounding + error.curvature * width ^ 2 / 8

def contourSeparation (p q : RationalComplex) : Rat :=
  max (min p.re q.re) (max (min (-p.re) (-q.re)) (max (min p.im q.im) (min (-p.im) (-q.im))))

def contourGap (error : ContourError) (width : Rat) (p q : RationalComplex) : Fin 4 → Rat :=
  fun component =>
    match component.val with
    | 0 => error.truncation
    | 1 => error.rounding
    | 2 => error.curvature * width ^ 2 / 8
    | _ => -contourSeparation p q

theorem contour_gap_sum (error : ContourError) (width : Rat) (p q : RationalComplex) :
    let g := contourGap error width p q
    g 0 + g 1 + g 2 + g 3 = error.margin width - contourSeparation p q := by
  rw [Rat.sub_eq_add_neg]
  rfl

theorem contour_separated_iff (threshold : Rat) (p q : RationalComplex) :
    Separated threshold p q ↔ threshold < contourSeparation p q := by
  simp only [contourSeparation, Separated, Std.lt_max_iff, Std.lt_min_iff]
  grind

theorem contour_mesh_component (error : ContourError) (width : Rat) :
    error.margin width - error.margin (width / 2) = 3 * error.curvature * width ^ 2 / 32 := by
  unfold ContourError.margin
  grind

def edgeQualifies (margin : Rat) (p q : RationalComplex) : Bool :=
  decide (Separated margin p q)

structure ContourVertex where
  position : RationalComplex
  image : RationalComplex

def contourMidpoint (evaluate : RationalComplex → RationalComplex) (p q : ContourVertex) :
    ContourVertex :=
  let position := (p.position.add q.position).scale (1 / 2)
  ⟨position, evaluate position⟩

/-- Return the signed crossing count and the number of admitted dyadic chords. -/
def dyadicContour (evaluate : RationalComplex → RationalComplex) (error : ContourError) :
    Nat → Rat → ContourVertex → ContourVertex → Option (Int × Nat)
  | depth, width, p, q =>
    if edgeQualifies (error.margin width) p.image q.image then
      some (crossing p.image q.image, 1)
    else
      match depth with
      | 0 => none
      | depth + 1 => do
        let mid := contourMidpoint evaluate p q
        let (leftWinding, leftChords) ← dyadicContour evaluate error depth (width / 2) p mid
        let (rightWinding, rightChords) ← dyadicContour evaluate error depth (width / 2) mid q
        return (leftWinding + rightWinding, leftChords + rightChords)

/-- Paths in the finite forward graph whose edges are qualified dyadic arcs. -/
inductive DyadicContourPath (evaluate : RationalComplex → RationalComplex) (error : ContourError) :
    Nat → Rat → ContourVertex → ContourVertex → (Int × Nat) → Prop where
  | chord {depth : Nat} {width : Rat} {p q : ContourVertex}
      (qualifies : edgeQualifies (error.margin width) p.image q.image = true) :
      DyadicContourPath evaluate error depth width p q (crossing p.image q.image, 1)
  | join {depth : Nat} {width : Rat} {p q : ContourVertex} {left right : Int × Nat}
      (first : DyadicContourPath evaluate error depth (width / 2) p (contourMidpoint evaluate p q) left)
      (second : DyadicContourPath evaluate error depth (width / 2) (contourMidpoint evaluate p q) q right) :
      DyadicContourPath evaluate error (depth + 1) width p q (left.1 + right.1, left.2 + right.2)

theorem edge_qualification_sound {margin : Rat} {p q : RationalComplex}
    (accepted : edgeQualifies margin p q = true) :
    Separated margin p q :=
  of_decide_eq_true accepted

theorem dyadic_contour_sound {evaluate : RationalComplex → RationalComplex} {error : ContourError} {depth : Nat}
    {width : Rat} {p q : ContourVertex} {result : Int × Nat}
    (accepted : dyadicContour evaluate error depth width p q = some result) :
    DyadicContourPath evaluate error depth width p q result := by
  induction depth generalizing width p q result with
  | zero =>
    rw [dyadicContour] at accepted
    split at accepted
    · rename_i qualifies
      cases accepted
      exact .chord qualifies
    · contradiction
  | succ depth ih =>
    rw [dyadicContour] at accepted
    split at accepted
    · rename_i qualifies
      cases accepted
      exact .chord qualifies
    · cases first : dyadicContour evaluate error depth (width / 2) p (contourMidpoint evaluate p q) with
      | none => simp [first] at accepted
      | some left =>
        cases second : dyadicContour evaluate error depth (width / 2) (contourMidpoint evaluate p q) q with
        | none => cases left; simp [first, second] at accepted
        | some right =>
          have firstPath := ih first
          have secondPath := ih second
          cases left
          cases right
          simp [first, second] at accepted
          rw [← accepted]
          exact .join firstPath secondPath

theorem DyadicContourPath.positive {evaluate : RationalComplex → RationalComplex} {error : ContourError} {depth : Nat}
    {width : Rat} {p q : ContourVertex} {result : Int × Nat}
    (path : DyadicContourPath evaluate error depth width p q result) :
    0 < result.2 := by
  induction path with
  | chord => exact Nat.zero_lt_succ 0
  | join first second firstPositive secondPositive => exact Nat.add_pos_left firstPositive _

theorem DyadicContourPath.optimal {evaluate : RationalComplex → RationalComplex} {error : ContourError} {depth : Nat}
    {width : Rat} {p q : ContourVertex} {result : Int × Nat}
    (path : DyadicContourPath evaluate error depth width p q result) :
    ∃ best, dyadicContour evaluate error depth width p q = some best ∧ best.2 ≤ result.2 := by
  induction path with
  | @chord depth width p q qualifies =>
    exact ⟨(crossing p.image q.image, 1),
      by rw [dyadicContour.eq_def]; simp [qualifies], Nat.le_refl _⟩
  | @join depth width p q left right first second firstOptimal secondOptimal =>
    by_cases qualifies : edgeQualifies (error.margin width) p.image q.image = true
    · exact ⟨(crossing p.image q.image, 1), by rw [dyadicContour]; simp [qualifies],
        Nat.add_pos_left first.positive right.2⟩
    · obtain ⟨⟨leftWinding, leftChords⟩, leftSelected, leftMinimum⟩ := firstOptimal
      obtain ⟨⟨rightWinding, rightChords⟩, rightSelected, rightMinimum⟩ := secondOptimal
      exact ⟨(leftWinding + rightWinding, leftChords + rightChords),
        by rw [dyadicContour]; simp [qualifies, leftSelected, rightSelected],
        Nat.add_le_add leftMinimum rightMinimum⟩

private def zetaError (bound cutoff logBound units exponentialError partialWeight decay : Rat) :
    ContourError :=
  let truncation :=
    bound ^ 2 * (bound + 1) * (bound + 2) * (bound + 3) / (2160 * cutoff ^ 3) * decay
  let weights := (cutoff - 1 / 2) * bound + cutoff + bound ^ 2 / (12 * cutoff) +
    bound ^ 2 * (bound + 1) * (bound + 2) / (720 * cutoff ^ 3)
  let rounding := weights * (exponentialError + 2 * bound / units)
  let logSquare := logBound ^ 2
  let b := bound + 2
  let tailCurvature := cutoff * logSquare +
    (logSquare * bound ^ 2 + 4 * logBound * bound + 2) / (12 * cutoff) +
    (logSquare * b ^ 4 + 8 * logBound * b ^ 3 + 12 * b ^ 2) / (720 * cutoff ^ 3)
  let curvature := partialWeight * (bound * logSquare + 2 * logBound) + decay * tailCurvature
  ⟨truncation, rounding, curvature⟩

private structure ZetaCut where
  left : ContourVertex
  right : ContourVertex
  winding : Int
  chords : Nat

private def zetaReader (left upper : Rat) (cutoff bits : Nat) :
    Option ((RationalComplex → RationalComplex) × (Rat → ContourError)) := do
  if valid : 2 ≤ cutoff ∧ 0 < bits then
    let units : Nat := 2 ^ bits
    let logBound := (cutoff - 1).log2 + 1
    let squarings := (((upper.ceil.toNat + 1) * logBound).log2) + 1
    let logTerms := (bits + (logBound + 1).log2 + 1) / 3 + 1
    let degree := ((List.range' 1 bits).find? (fun d => units ≤ (List.range' 1 (d + 1)).prod)).getD bits
    let exponentialError : Rat := (((4 * degree + 3) * 3 ^ squarings - 1 : Nat) : Rat) / (units : Rat)
    if 1 ≤ exponentialError then none
    else
      let logs := (List.range (cutoff - 1)).map (fun n => logGrid units logTerms (n + 1) (Nat.succ_pos n))
      let tailLog := logGrid units logTerms cutoff (by omega)
      let weights : Rat × Rat :=
        if 1 / 2 ≤ left then
          let root := cutoff.sqrt
          (min ((cutoff : Rat) - 1 / 2) (2 * ((root + 1 : Nat) : Rat)), 1 / (root : Rat))
        else ((cutoff : Rat) - 1 / 2, 1)
      return (zetaValue units squarings degree cutoff logs tailLog, fun y =>
        zetaError (y.ceil.toNat + 1 : Nat) cutoff logBound units exponentialError weights.1 weights.2)
  else none

/-- Dyadic sign brackets at a common width, clipped to the endpoints of their band. -/
structure CriticalSignBatch where
  lower : Nat
  upper : Nat
  cutoff : Nat
  bits : Nat
  indices : List Nat

def CriticalSignBatch.brackets (batch : CriticalSignBatch) : List (Rat × Rat) :=
  batch.indices.map fun (n : Nat) =>
    (max (batch.lower : Rat) ((2 * (n : Rat) - 1) / 64),
     min (batch.upper : Rat) ((2 * (n : Rat) + 3) / 64))

def criticalLineBatches : List CriticalSignBatch :=
  [⟨192, 384, 1536, 58, [
     6144, 6178, 6248, 6300, 6336, 6440, 6479, 6534, 6572, 6653, 6706, 6774, 6827, 6865, 6917,
     7010, 7062, 7085, 7168, 7199, 7277, 7338, 7400, 7423, 7478, 7568, 7608, 7665, 7713, 7770,
     7810, 7908, 7939, 7986, 8032, 8098, 8169, 8204, 8275, 8315, 8345, 8434, 8497, 8531, 8573,
     8639, 8687, 8750, 8818, 8846, 8904, 8935, 9038, 9062, 9114, 9173, 9213, 9266, 9339, 9393,
     9438, 9458, 9535, 9594, 9652, 9686, 9755, 9783, 9831, 9923, 9957, 9997, 10047, 10095, 10167,
     10203, 10277, 10308, 10350, 10395, 10478, 10529, 10558, 10607, 10676, 10694, 10778, 10826, 10875, 10913,
     10945, 11029, 11083, 11112, 11178, 11213, 11260, 11311, 11392, 11428, 11454, 11511, 11561, 11626, 11671,
     11718, 11775, 11806, 11841, 11937, 11963, 12026, 12042, 12109, 12155, 12207, 12270]⟩,
   ⟨384, 620, 2560, 60, [
     12318, 12347, 12391, 12443, 12526, 12551, 12589, 12658, 12684, 12733, 12799, 12858, 12891, 12935, 12964,
     13042, 13086, 13136, 13183, 13224, 13280, 13294, 13388, 13435, 13460, 13506, 13558, 13602, 13670, 13700,
     13770, 13801, 13828, 13884, 13957, 14002, 14035, 14077, 14133, 14172, 14218, 14299, 14318, 14372, 14404,
     14444, 14527, 14559, 14602, 14652, 14704, 14722, 14786, 14849, 14901, 14930, 14958, 15025, 15064, 15129,
     15162, 15219, 15256, 15298, 15326, 15418, 15450, 15483, 15537, 15568, 15628, 15669, 15724, 15786, 15806,
     15851, 15885, 15954, 16009, 16051, 16072, 16143, 16173, 16206, 16281, 16328, 16369, 16403, 16437, 16493,
     16562, 16583, 16643, 16688, 16718, 16766, 16802, 16892, 16908, 16953, 16987, 17046, 17080, 17141, 17186,
     17229, 17286, 17300, 17339, 17418, 17460, 17504, 17533, 17583, 17631, 17665, 17720, 17785, 17820, 17842,
     17898, 17927, 18001, 18053, 18064, 18134, 18167, 18205, 18241, 18317, 18355, 18403, 18425, 18465, 18531,
     18564, 18622, 18663, 18705, 18751, 18775, 18820, 18901, 18935, 18962, 19007, 19063, 19083, 19151, 19185,
     19251, 19282, 19316, 19347, 19404, 19469, 19500, 19546, 19576, 19635, 19668, 19697, 19779, 19813]⟩,
   ⟨620, 854, 3584, 62, [
     19848, 19894, 19916, 19976, 20032, 20072, 20106, 20175, 20185, 20231, 20273, 20336, 20396, 20413, 20445,
     20502, 20542, 20584, 20639, 20683, 20728, 20761, 20806, 20821, 20916, 20937, 20982, 21022, 21061, 21109,
     21142, 21193, 21255, 21290, 21328, 21348, 21407, 21450, 21518, 21537, 21579, 21636, 21671, 21689, 21751,
     21820, 21843, 21888, 21919, 21957, 22014, 22059, 22095, 22158, 22181, 22225, 22263, 22292, 22372, 22409,
     22441, 22471, 22529, 22564, 22597, 22664, 22695, 22756, 22780, 22807, 22850, 22915, 22959, 22999, 23030,
     23083, 23112, 23163, 23186, 23265, 23308, 23320, 23373, 23405, 23450, 23513, 23544, 23585, 23634, 23677,
     23698, 23736, 23804, 23851, 23887, 23925, 23943, 24020, 24030, 24092, 24138, 24186, 24216, 24259, 24284,
     24329, 24406, 24434, 24457, 24514, 24550, 24585, 24630, 24674, 24734, 24771, 24801, 24831, 24873, 24933,
     24971, 25028, 25043, 25097, 25143, 25166, 25198, 25281, 25306, 25357, 25372, 25423, 25459, 25512, 25558,
     25588, 25651, 25681, 25703, 25752, 25787, 25860, 25894, 25922, 25957, 26008, 26049, 26075, 26135, 26188,
     26214, 26263, 26294, 26310, 26384, 26433, 26460, 26506, 26541, 26588, 26617, 26656, 26708, 26774, 26795,
     26823, 26862, 26913, 26945, 27013, 27033, 27078, 27135, 27151, 27195, 27220, 27301]⟩,
   ⟨854, 1024, 4096, 62, [
     27331, 27369, 27407, 27433, 27484, 27533, 27557, 27622, 27658, 27699, 27725, 27766, 27797, 27867, 27910,
     27939, 27965, 28031, 28051, 28084, 28140, 28186, 28236, 28269, 28294, 28328, 28379, 28431, 28471, 28506,
     28556, 28579, 28636, 28652, 28692, 28775, 28795, 28827, 28871, 28899, 28950, 28986, 29045, 29066, 29125,
     29159, 29194, 29210, 29271, 29323, 29370, 29402, 29422, 29477, 29520, 29545, 29592, 29649, 29691, 29717,
     29755, 29792, 29819, 29900, 29919, 29959, 30001, 30048, 30069, 30117, 30145, 30214, 30250, 30296, 30306,
     30347, 30404, 30433, 30487, 30532, 30554, 30613, 30640, 30669, 30702, 30773, 30821, 30834, 30881, 30915,
     30955, 30996, 31044, 31074, 31141, 31163, 31192, 31237, 31261, 31320, 31378, 31401, 31436, 31474, 31525,
     31556, 31576, 31647, 31687, 31723, 31767, 31782, 31820, 31878, 31920, 31962, 31993, 32043, 32076, 32104,
     32149, 32177, 32256, 32281, 32313, 32338, 32397, 32417, 32470, 32513, 32552, 32595, 32637, 32669, 32689,
     32732]⟩,
   ⟨1024, 1232, 5120, 64, [
     32808, 32822, 32878, 32900, 32935, 32988, 33018, 33050, 33107, 33158, 33184, 33218, 33250, 33288, 33331,
     33395, 33424, 33443, 33506, 33535, 33566, 33599, 33650, 33703, 33752, 33760, 33814, 33827, 33892, 33924,
     33968, 34013, 34050, 34083, 34126, 34157, 34175, 34257, 34291, 34321, 34354, 34391, 34440, 34461, 34516,
     34553, 34597, 34654, 34665, 34693, 34740, 34781, 34840, 34873, 34907, 34935, 34990, 35017, 35053, 35084,
     35162, 35179, 35218, 35258, 35281, 35319, 35379, 35416, 35448, 35493, 35534, 35566, 35597, 35628, 35682,
     35737, 35774, 35797, 35823, 35876, 35918, 35939, 36010, 36024, 36085, 36109, 36151, 36172, 36207, 36278,
     36316, 36337, 36381, 36420, 36447, 36503, 36520, 36571, 36633, 36655, 36690, 36720, 36755, 36799, 36850,
     36894, 36924, 36950, 37011, 37037, 37056, 37103, 37164, 37199, 37238, 37271, 37288, 37342, 37378, 37430,
     37454, 37507, 37545, 37575, 37606, 37652, 37667, 37750, 37780, 37800, 37842, 37878, 37924, 37948, 37995,
     38043, 38078, 38127, 38150, 38186, 38203, 38273, 38306, 38357, 38379, 38417, 38457, 38500, 38523, 38559,
     38619, 38671, 38687, 38716, 38765, 38787, 38835, 38892, 38917, 38949, 39009, 39027, 39066, 39094, 39134,
     39200, 39227, 39271, 39293, 39321, 39378, 39409]⟩,
   ⟨1232, 1270, 6144, 66, [
     39440, 39496, 39536, 39564, 39615, 39630, 39663, 39706, 39778, 39793, 39835, 39860,
     39915, 39938, 39973, 40021, 40053, 40117, 40141, 40173, 40197, 40241, 40280, 40331,
     40371, 40401, 40437, 40478, 40517, 40550, 40562]⟩]

theorem critical_line_batch_sizes :
    criticalLineBatches.map (fun batch => batch.brackets.length) = [117, 164, 177, 136, 172, 31] := by
  decide +kernel

def zetaBands (left right : Rat) (heights : List Rat) (cutoff bits depth : Nat) :
    Option (List (Int × Nat) × Nat) := do
  let lower :: next :: rest := heights | none
  let upper := rest.getLastD next
  if 0 ≤ left ∧ left < right ∧ right ≤ 1 ∧ 6 ≤ lower ∧ lower < upper then
      let (evaluate, errorAt) ← zetaReader left upper cutoff bits
      let vertex := fun position => (⟨position, evaluate position⟩ : ContourVertex)
      let cutAt := fun (y : Rat) => do
        let p := vertex ⟨left, y⟩
        let q := vertex ⟨right, y⟩
        let (winding, chords) ← dyadicContour evaluate (errorAt y) depth (right - left) p q
        return (⟨p, q, winding, chords⟩ : ZetaCut)
      let ascent := fun (p q : ContourVertex) => do
        let rise := q.position.im - p.position.im
        let steps := rise.ceil.toNat
        let width := rise / (steps : Rat)
        let inside := (List.range' 1 (steps - 1)).map (fun (step : Nat) =>
          vertex ⟨p.position.re, p.position.im + (step : Rat) * width⟩)
        let arcs := (p :: inside).zip (inside ++ [q])
        arcs.foldlM (fun (winding, chords) (a, b) => do
          let (arcCount, arcChords) ← dyadicContour evaluate (errorAt b.position.im) depth width a b
          return (winding + arcCount, chords + arcChords)) (0, 0)
      let bottom ← cutAt lower
      let (_, counts, evaluations) ← (next :: rest).foldlM (fun (previous, counts, evaluations) y => do
        if previous.left.position.im < y ∧ y ≤ upper then
          let top ← cutAt y
          let (rightCount, rightChords) ← ascent previous.right top.right
          let (leftCount, leftChords) ← ascent previous.left top.left
          let winding := previous.winding + rightCount - top.winding - leftCount
          let chords := previous.chords + top.chords + rightChords + leftChords
          let added := top.chords + 1 + (rightChords - 1) + (leftChords - 1)
          return (top, (winding, chords) :: counts, evaluations + added)
        else none) (bottom, [], bottom.chords + 1)
      return (counts.reverse, evaluations)
  else none

private def phaseArctanSum (x : Rat) (terms : Nat) : Rat :=
  rationalPartialSum (fun k => (-1 : Rat) ^ k * x ^ (2 * k + 1) / (2 * (k : Rat) + 1)) terms

private def phasePiLower : Rat := 314159 / 100000
private def phasePiUpper : Rat := 314160 / 100000

theorem phase_pi_caps :
    phasePiLower ≤ 16 * phaseArctanSum (1 / 5) 6 - 4 * phaseArctanSum (1 / 239) 7 ∧
    16 * phaseArctanSum (1 / 5) 7 - 4 * phaseArctanSum (1 / 239) 6 ≤ phasePiUpper := by
  decide +kernel

private def phaseLogBounds (ratio : Rat) : RationalInterval :=
  let exponent := ratio.floor.toNat.log2
  let mantissa := ratio / (2 ^ exponent : Nat)
  let shifted := atanhLogBounds ((mantissa - 1) / (mantissa + 1)) 14
  let lnTwo := atanhLogBounds (1 / 3) 14
  ⟨shifted.lower + (exponent : Rat) * lnTwo.lower,
   shifted.upper + (exponent : Rat) * lnTwo.upper⟩

private def criticalPhaseIndex (height : Rat) (turns quadrant : Int) : Option Int := do
  let half := height / 2
  let lower := half * ((phaseLogBounds (half / phasePiUpper)).lower - 1) - 5 / (16 * half)
  let upper := half * ((phaseLogBounds (half / phasePiLower)).upper - 1) + 1 / (32 * half)
  let floorAngle := lower / phasePiUpper + 3 / 8 + (quadrant : Rat) / 2
  let ceilAngle := upper / phasePiLower + 3 / 8 + ((quadrant + 1 : Int) : Rat) / 2
  let index := floorAngle.ceil
  if 0 ≤ lower ∧ (index : Rat) ≤ ceilAngle ∧ ceilAngle < (index : Rat) + 1 then
    some (index + 2 * turns)
  else none

/-- Return the index on the critical line and the number of certified horizontal chords. -/
def zetaCriticalIndex (height : Rat) (cutoff bits depth : Nat) : Option (Int × Nat) := do
  if 24 ≤ height then
    let (evaluate, errorAt) ← zetaReader (1 / 2) height cutoff bits
    let error := errorAt height
    let margin := error.margin 0
    let start : RationalComplex := ⟨2, height⟩
    let endPoint : RationalComplex := ⟨1 / 2, height⟩
    let readRotated := fun z => (evaluate z).scale (-1)
    let right := readRotated start
    let left := readRotated endPoint
    if right.re < -margin ∨ margin < max right.im (-right.im) then
      let quadrant ←
        if left.re < -margin then
          if left.im < -margin then some (0 : Int) else if margin < left.im then some (-1) else none
        else if margin < left.re then
          if left.im < -margin then some 1 else if margin < left.im then some (-2) else none
        else none
      let (turns, chords) ← dyadicContour readRotated error depth (3 / 2) ⟨start, right⟩ ⟨endPoint, left⟩
      let index ← criticalPhaseIndex height turns quadrant
      return (index, chords)
    else none
  else none

private def coordinateMass (z : RationalComplex) : Rat :=
  max z.re (-z.re) + max z.im (-z.im)

private def criticalDotUpper (p q : RationalComplex) (firstError secondError : Rat) : Rat :=
  p.re * q.re + p.im * q.im + firstError * coordinateMass q +
    secondError * coordinateMass p + 2 * firstError * secondError

private theorem multiplied_coordinate_error (error coordinate multiplier : Rat)
    (lower : -error ≤ coordinate) (upper : coordinate ≤ error) :
    coordinate * multiplier ≤ error * max multiplier (-multiplier) := by
  have errorNonnegative : 0 ≤ error := by grind
  by_cases nonnegative : 0 ≤ multiplier
  · have controlled := Rat.mul_le_mul_of_nonneg_right upper nonnegative
    exact Rat.le_trans controlled (Rat.mul_le_mul_of_nonneg_left Std.left_le_max errorNonnegative)
  · have withinMax := Rat.mul_le_mul_of_nonneg_left
      (Std.right_le_max : -multiplier ≤ max multiplier (-multiplier)) errorNonnegative
    have controlled := Rat.mul_le_mul_of_nonneg_right
      (show -coordinate ≤ error by grind) (show 0 ≤ -multiplier by grind)
    grind

theorem critical_dot_upper_bound (p q exactP exactQ : RationalComplex) (firstError secondError : Rat)
    (nonnegative : 0 ≤ firstError)
    (firstRe : -firstError ≤ exactP.re - p.re ∧ exactP.re - p.re ≤ firstError)
    (firstIm : -firstError ≤ exactP.im - p.im ∧ exactP.im - p.im ≤ firstError)
    (secondRe : -secondError ≤ exactQ.re - q.re ∧ exactQ.re - q.re ≤ secondError)
    (secondIm : -secondError ≤ exactQ.im - q.im ∧ exactQ.im - q.im ≤ secondError) :
    exactP.re * exactQ.re + exactP.im * exactQ.im ≤ criticalDotUpper p q firstError secondError := by
  have productBound (a b dx dy : Rat) (boundX : -firstError ≤ dx ∧ dx ≤ firstError)
      (boundY : -secondError ≤ dy ∧ dy ≤ secondError) :
      (a + dx) * (b + dy) ≤ a * b +
        firstError * max b (-b) + secondError * max a (-a) + firstError * secondError := by
    have xTerm := multiplied_coordinate_error firstError dx b boundX.1 boundX.2
    have yTerm := multiplied_coordinate_error secondError dy a boundY.1 boundY.2
    have both := multiplied_coordinate_error firstError dx dy boundX.1 boundX.2
    have maxDy : max dy (-dy) ≤ secondError := Std.max_le_iff.mpr ⟨boundY.2, by grind⟩
    have remainder := Rat.mul_le_mul_of_nonneg_left maxDy nonnegative
    grind
  have realBound := productBound p.re q.re (exactP.re - p.re) (exactQ.re - q.re) firstRe secondRe
  have imaginaryBound := productBound p.im q.im (exactP.im - p.im) (exactQ.im - q.im) firstIm secondIm
  dsimp [criticalDotUpper, coordinateMass]
  grind

/-- Check disjoint critical-line sign brackets, using the same logarithm table at all endpoints. -/
def zetaCriticalSignTests (lower upper : Rat) (brackets : List (Rat × Rat)) (cutoff bits : Nat) :
    Option (List Bool) := do
  if 6 ≤ lower ∧ lower < upper then
    let (evaluate, errorAt) ← zetaReader (1 / 2) upper cutoff bits
    let phaseScale : Rat := (upper.ceil.toNat.log2 + 2 : Nat)
    let (_, checks) ← brackets.foldlM (fun (previous, checks) (a, b) => do
      if previous ≤ a ∧ a < b ∧ b ≤ upper ∧ phaseScale * (b - a) ≤ 1 then
        let p := evaluate ⟨1 / 2, a⟩
        let q := evaluate ⟨1 / 2, b⟩
        let upperDot := criticalDotUpper p q ((errorAt a).margin 0) ((errorAt b).margin 0)
        return (b, decide (upperDot < 0) :: checks)
      else none) (lower, [])
    return checks.reverse
  else none

structure XiInterpolationAnchor where
  heightLower64 : Nat
  heightUpper64 : Nat
  rateLower : Nat
  rateUpper : Nat
  weightUpper : Nat

def xiInterpolationAnchors : List XiInterpolationAnchor :=
  [
    ⟨384, 1152, 38, 327, 2⟩,
    ⟨1536, 1792, 578, 787, 2⟩,
    ⟨2048, 2240, 1026, 1228, 2⟩,
    ⟨2496, 2688, 1523, 1767, 2⟩,
    ⟨2944, 3136, 2118, 2404, 2⟩,
    ⟨3264, 3520, 2603, 3028, 2⟩,
    ⟨3712, 3840, 3366, 3603, 2⟩,
    ⟨4096, 4224, 4098, 4359, 2⟩,
    ⟨4352, 4544, 4626, 5044, 2⟩,
    ⟨4736, 4864, 5478, 5779, 2⟩,
    ⟨5632, 5824, 7746, 8284, 2⟩,
    ⟨6784, 6976, 11238, 11884, 2⟩,
    ⟨8344, 8464, 16999, 17493, 9⟩,
    ⟨10128, 10248, 25045, 25643, 824⟩,
    ⟨12495, 12499, 38118, 38144, 35885⟩,
    ⟨15135, 15139, 55927, 55957, 1525172⟩,
    ⟨18227, 18231, 81111, 81148, 22442921⟩,
    ⟨22165, 22169, 119945, 119989, 130132215⟩,
    ⟨26919, 26923, 176914, 176968, 226049257⟩,
    ⟨32655, 32659, 260341, 260406, 63201253⟩
  ]

private def interpolationGap (a b : XiInterpolationAnchor) : Nat :=
  if a.rateUpper < b.rateLower then b.rateLower - a.rateUpper
  else a.rateLower - b.rateUpper

private def interpolationWeightUpper (anchor : XiInterpolationAnchor) : Rat :=
  let others := xiInterpolationAnchors.filter (fun row => row.rateLower != anchor.rateLower)
  let product := others.foldl
    (fun factor row => factor * ((anchor.rateUpper : Rat) / (interpolationGap anchor row : Rat))) 1
  let rateSum : Nat := others.foldl (fun total row => total + row.rateUpper) 0
  (anchor.rateUpper : Rat) *
    ((1 + 1 / (anchor.rateLower : Rat)) ^ 20 * product *
      (51 / 100 + (20 + (rateSum : Rat)) / (1270 * 1270))) ^ 2

theorem xi_twenty_node_anchor_certificate :
    xiInterpolationAnchors.length = 20 ∧
    (xiInterpolationAnchors.zip (xiInterpolationAnchors.drop 1)).all
      (fun (a, b) => decide (a.rateUpper < b.rateLower)) = true ∧
    xiInterpolationAnchors.all
      (fun a => decide
        (0 < a.rateLower ∧
          (a.rateLower : Rat) ≤ ((a.heightLower64 : Rat) / 64) ^ 2 + 9 / 4 ∧
          ((a.heightUpper64 : Rat) / 64) ^ 2 + 9 / 4 ≤ (a.rateUpper : Rat) ∧
          a.rateUpper ≤ 2 * (1270 * 1270) ∧
          interpolationWeightUpper a ≤ (a.weightUpper : Rat))) = true ∧
    (xiInterpolationAnchors.drop 14).all
      (fun a => criticalLineBatches.any (fun band =>
        band.brackets.contains
          (((a.heightLower64 : Rat) / 64), ((a.heightUpper64 : Rat) / 64)))) = true ∧
    xiInterpolationAnchors.foldl (fun sum a => sum + a.weightUpper) 0 < 444000000 := by
  decide +kernel

end RationalComplex

theorem unique_zero_fixed_under_reflection {Point : Type _} (reflect : Point → Point)
    (inside isZero : Point → Prop)
    (preserves : ∀ p, inside p → isZero p → inside (reflect p) ∧ isZero (reflect p))
    (unique : ∀ p q, inside p → isZero p → inside q → isZero q → p = q)
    {p : Point} (member : inside p) (root : isZero p) : reflect p = p := by
  obtain ⟨other_member, other_root⟩ := preserves p member root
  exact unique _ _ other_member other_root member root

theorem xi_ray_window_endpoint : (9 / 4 : Rat) * 715716 = 1269 ^ 2 := by
  decide +kernel

end GAlgebra
