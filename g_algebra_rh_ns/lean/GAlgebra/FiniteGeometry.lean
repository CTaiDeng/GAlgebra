import GAlgebra.Coverage

set_option autoImplicit false
namespace GAlgebra

theorem finiteSum_zero_of_members {I V : Type _} [Abelian V] {f : I → V}
    (is : List I) (zero : ∀ i, i ∈ is → f i = 0) : finiteSum f is = 0 := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    have hi := zero i List.mem_cons_self
    have ht := ih (fun j hj => zero j (List.mem_cons_of_mem i hj))
    simp only [finiteSum, hi, ht, Abelian.zero_add]

theorem finiteSum_single_of_nodup {I V : Type _} [Abelian V] (f : I → V)
    {is : List I} {a : I} (nd : is.Nodup) (ha : a ∈ is)
    (others : ∀ i, i ∈ is → i ≠ a → f i = 0) : finiteSum f is = f a := by
  classical
  induction is with
  | nil => simp at ha
  | cons i is ih =>
    obtain ⟨notMem, ndTail⟩ := List.nodup_cons.mp nd
    by_cases e : i = a
    · subst i
      have tail_zero := finiteSum_zero_of_members is (fun j hj =>
        others j (List.mem_cons_of_mem a hj) (fun eq => notMem (eq ▸ hj)))
      simp only [finiteSum, tail_zero, Abelian.add_zero]
    · have ha' : a ∈ is := (List.mem_cons.mp ha).resolve_left (fun h => e h.symm)
      have hi := others i List.mem_cons_self e
      have ht := ih ndTail ha' (fun j hj => others j (List.mem_cons_of_mem i hj))
      simp only [finiteSum, hi, ht, Abelian.zero_add]

structure ScalarGeometry {K V : Type _} [Abelian K] [Abelian V] [Mul K]
    (P : Pairing K V) where
  scale : K → V → V
  zero_scale : ∀ x, scale 0 x = 0
  scale_add : ∀ c x y, scale c (x + y) = scale c x + scale c y
  add_scale : ∀ a b x, scale (a + b) x = scale a x + scale b x
  dot_scale : ∀ a x y, P.dot (scale a x) y = a * P.dot x y
  mul_zero : ∀ a : K, a * 0 = 0
  divideBy : K → AddMap K K
  cancel_division : ∀ d : K, d ≠ 0 → ∀ c : K, divideBy d c * d = c

namespace ScalarGeometry

variable {K V : Type _} [Abelian K] [Abelian V] [Mul K]
variable {P : Pairing K V} (G : ScalarGeometry P)

structure Frame (S : Subgroup V) where
  vectors : List V
  distinct : vectors.Nodup
  inSpace : ∀ e, e ∈ vectors → S.mem e
  scaleClosed : ∀ c x, S.mem x → S.mem (G.scale c x)
  diagonal : ∀ e, e ∈ vectors → P.dot e e ≠ 0
  offDiagonal : ∀ e f, e ∈ vectors → f ∈ vectors → e ≠ f → P.dot e f = 0
  spans : ∀ x, S.mem x → ∃ coeffs : List (K × V),
    (∀ p, p ∈ coeffs → p.2 ∈ vectors) ∧
    finiteSum (fun p => G.scale p.1 p.2) coeffs = x

variable {S : Subgroup V}

def component (e : V) : AddMap V V where
  toFun x := G.scale (G.divideBy (P.dot e e) (P.dot x e)) e
  zero := by rw [P.zero_left, AddMap.map_zero, G.zero_scale]
  add x y := by rw [P.add_left, AddMap.map_add, G.add_scale]

def ontoFrame (F : G.Frame S) : AddMap V V where
  toFun x := finiteSum (fun e => G.component e x) F.vectors
  zero := finiteSum_zero_of_members F.vectors (fun e _ => (G.component e).map_zero)
  add x y := by
    have step : ∀ l : List V,
        finiteSum (fun e => G.component e (x + y)) l =
          finiteSum (fun e => G.component e x) l + finiteSum (fun e => G.component e y) l := by
      intro l
      induction l with
      | nil => simp [finiteSum]
      | cons e es ih =>
        simp only [finiteSum, (G.component e).map_add, ih]
        exact Abelian.swap_middle _ _ _ _
    exact step F.vectors

theorem ontoFrame_in_space (F : G.Frame S) (x : V) : S.mem (G.ontoFrame F x) := by
  have sum : ∀ l : List V, (∀ e, e ∈ l → e ∈ F.vectors) →
      S.mem (finiteSum (fun e => G.component e x) l) := by
    intro l
    induction l with
    | nil => intro _; exact S.zero
    | cons e es ih =>
      intro included
      have he := F.inSpace e (included e List.mem_cons_self)
      exact S.add (F.scaleClosed _ _ he)
        (ih (fun z hz => included z (List.mem_cons_of_mem e hz)))
  exact sum F.vectors (fun _ h => h)

theorem ontoFrame_agrees_on_basis (F : G.Frame S) (x e : V) (he : e ∈ F.vectors) :
    P.dot (G.ontoFrame F x) e = P.dot x e := by
  let term := fun b => P.dot (G.component b x) e
  have hsingle : finiteSum term F.vectors = term e := by
    apply finiteSum_single_of_nodup term F.distinct he
    intro b hb hne
    change P.dot (G.scale (G.divideBy (P.dot b b) (P.dot x b)) b) e = 0
    rw [G.dot_scale, F.offDiagonal b e hb he hne, G.mul_zero]
  have hmap : P.dot (G.ontoFrame F x) e = finiteSum term F.vectors := by
    rw [← P.left_eq]
    change P.left e (finiteSum (fun b => G.component b x) F.vectors) = finiteSum term F.vectors
    rw [finiteSum_map]
    exact finiteSum_congr (fun b => P.left_eq (G.component b x) e) F.vectors
  rw [hmap, hsingle]
  change P.dot (G.scale (G.divideBy (P.dot e e) (P.dot x e)) e) e = P.dot x e
  rw [G.dot_scale, G.cancel_division _ (F.diagonal e he)]

theorem perpendicular_from_basis (F : G.Frame S) (v : V)
    (h : ∀ e, e ∈ F.vectors → P.dot e v = 0) : P.Perp S v := by
  intro x hx
  obtain ⟨cs, hs, hsum⟩ := F.spans x hx
  rw [← hsum, ← P.left_eq, finiteSum_map]
  apply finiteSum_zero_of_members
  intro p hp
  rw [P.left_eq, G.dot_scale, h _ (hs _ hp), G.mul_zero]

def frameRemainder (F : G.Frame S) : AddMap V V where
  toFun x := x + -(G.ontoFrame F x)
  zero := by simp only [AddMap.map_zero, Abelian.neg_zero, Abelian.zero_add]
  add x y := by
    simp only [AddMap.map_add, Abelian.neg_add_rev]
    rw [Abelian.comm (-(G.ontoFrame F y)), Abelian.swap_middle]

theorem remainder_perpendicular (F : G.Frame S) (v : V) :
    P.Perp S (G.frameRemainder F v) := by
  apply G.perpendicular_from_basis F
  intro e he
  change P.dot e (v + -(G.ontoFrame F v)) = 0
  rw [P.add_right, P.neg_right, P.symmetric e v, P.symmetric e (G.ontoFrame F v),
    G.ontoFrame_agrees_on_basis F v e he, Abelian.add_neg]

def frame_splitting (F : G.Frame S) : OrthogonalSplitting P S where
  project := G.frameRemainder F
  vanishes x hx := by
    have hm : S.mem (G.frameRemainder F x) := S.add hx (S.neg (G.ontoFrame_in_space F x))
    exact P.definite _ (G.remainder_perpendicular F x _ hm)
  residual x := by
    change S.mem (x + -(x + -(G.ontoFrame F x)))
    rw [Abelian.neg_add_rev, Abelian.neg_neg, Abelian.comm (G.ontoFrame F x) (-x),
      ← Abelian.assoc, Abelian.add_neg, Abelian.zero_add]
    exact G.ontoFrame_in_space F x
  lands := G.remainder_perpendicular F

theorem orthogonal_extension_step (F : G.Frame S) (x : V) (hx : ¬ S.mem x) :
    G.frameRemainder F x ≠ 0 ∧ P.Perp S (G.frameRemainder F x) ∧
    ∀ v, (∃ s c, S.mem s ∧ s + G.scale c x = v) ↔
      (∃ s c, S.mem s ∧ s + G.scale c (G.frameRemainder F x) = v) := by
  let p := G.ontoFrame F x
  let r := G.frameRemainder F x
  have p_mem : S.mem p := G.ontoFrame_in_space F x
  have xr : p + r = x := by
    change p + (x + -p) = x
    rw [← Abelian.assoc, Abelian.comm p x, Abelian.assoc, Abelian.add_neg, Abelian.add_zero]
  refine ⟨?_, G.remainder_perpendicular F x, ?_⟩
  · intro h
    change r = 0 at h
    rw [h, Abelian.add_zero] at xr
    exact hx (xr ▸ p_mem)
  · intro v
    constructor
    · rintro ⟨s, c, hs, hv⟩
      refine ⟨s + G.scale c p, c, S.add hs (F.scaleClosed c p p_mem), ?_⟩
      rw [Abelian.assoc, ← G.scale_add, xr, hv]
    · rintro ⟨s, c, hs, hv⟩
      refine ⟨s + -G.scale c p, c, S.add hs (S.neg (F.scaleClosed c p p_mem)), ?_⟩
      have hstep : (s + -G.scale c p) + G.scale c (p + r) = s + G.scale c r := by
        rw [G.scale_add, Abelian.assoc, ← Abelian.assoc (-G.scale c p),
          Abelian.neg_add, Abelian.zero_add]
      exact (congrArg (fun z => (s + -G.scale c p) + G.scale c z) xr.symm).trans
        (hstep.trans hv)

end ScalarGeometry

theorem frame_projected_jacgap_descent {V : Type _} [Abelian V] {P : Pairing Rat V}
    (geometry : ScalarGeometry P) {S : Subgroup V} (frame : geometry.Frame S) (gradient : V)
    (covered : P.dot (geometry.frameRemainder frame gradient) (geometry.frameRemainder frame gradient)
      < P.dot gradient gradient) :
    P.dot gradient (-(geometry.ontoFrame frame gradient)) < 0 := by
  let projected := geometry.ontoFrame frame gradient
  let remainder := geometry.frameRemainder frame gradient
  have decomposition : projected + remainder = gradient := by
    change projected + (gradient + -projected) = gradient
    rw [← Abelian.assoc, Abelian.comm projected gradient, Abelian.assoc,
      Abelian.add_neg, Abelian.add_zero]
  have orthogonal : P.dot projected remainder = 0 :=
    geometry.remainder_perpendicular frame gradient _ (geometry.ontoFrame_in_space frame gradient)
  have reverse : P.dot remainder projected = 0 := (P.symmetric _ _).trans orthogonal
  have energy : P.dot gradient gradient = P.dot projected projected + P.dot remainder remainder := by
    calc
      _ = P.dot (projected + remainder) (projected + remainder) :=
        congrArg (fun x => P.dot x x) decomposition.symm
      _ = _ := by rw [P.add_left, P.add_right projected, P.add_right remainder,
                      orthogonal, reverse, Abelian.add_zero, Abelian.zero_add]
  have along : P.dot gradient projected = P.dot projected projected := by
    calc
      _ = P.dot (projected + remainder) projected :=
        congrArg (fun x => P.dot x projected) decomposition.symm
      _ = _ := by rw [P.add_left, reverse, Abelian.add_zero]
  change P.dot remainder remainder < P.dot gradient gradient at covered
  change P.dot gradient (-projected) < 0
  rw [P.neg_right, along]
  grind

theorem contour_finite_upper_bound {I : Type _} (xs : List I)
    (values bounds : I → Rat) (controls : ∀ i, i ∈ xs → values i ≤ bounds i) :
    finiteSum values xs ≤ finiteSum bounds xs := by
  induction xs with
  | nil => change (0 : Rat) ≤ 0; decide
  | cons i is ih =>
    have first := controls i List.mem_cons_self
    have rest := ih (fun j hj => controls j (List.mem_cons_of_mem i hj))
    change values i + finiteSum values is ≤ bounds i + finiteSum bounds is
    grind

private theorem finite_sum_add {I V : Type _} [Abelian V] (xs : List I) (f g : I → V) :
    finiteSum (fun i => f i + g i) xs = finiteSum f xs + finiteSum g xs := by
  induction xs with
  | nil => change (0 : V) = 0 + 0; rw [Abelian.zero_add]
  | cons i rest ih =>
    change f i + g i + finiteSum (fun j => f j + g j) rest =
      (f i + finiteSum f rest) + (g i + finiteSum g rest)
    rw [ih]
    exact Abelian.swap_middle _ _ _ _

theorem finite_sum_swap {I J V : Type _} [Abelian V] (rows : List I) (columns : List J)
    (f : I → J → V) :
    finiteSum (fun i => finiteSum (f i) columns) rows =
      finiteSum (fun j => finiteSum (fun i => f i j) rows) columns := by
  induction rows with
  | nil =>
    change (0 : V) = finiteSum (fun _ : J => (0 : V)) columns
    symm
    exact finiteSum_zero_of_members columns (fun _ _ => rfl)
  | cons i rest ih =>
    change finiteSum (f i) columns + finiteSum (fun k => finiteSum (f k) columns) rest =
      finiteSum (fun j => f i j + finiteSum (fun k => f k j) rest) columns
    rw [ih, finite_sum_add]

theorem finite_row_dual_transport {I J : Type _} (rows : List I) (columns : List J)
    (matrix : I → J → Rat) (test : I → Rat) (value : J → Rat) :
    finiteSum (fun i => test i * finiteSum (fun j => matrix i j * value j) columns) rows =
      finiteSum (fun j => finiteSum (fun i => test i * matrix i j) rows * value j) columns := by
  calc
    _ = finiteSum (fun i => finiteSum (fun j => test i * (matrix i j * value j)) columns) rows := by
      apply finiteSum_congr
      intro i
      let scale : AddMap Rat Rat := ⟨fun x => test i * x, by grind, by intro a b; grind⟩
      exact finiteSum_map scale _ columns
    _ = finiteSum (fun j => finiteSum (fun i => test i * (matrix i j * value j)) rows) columns :=
      finite_sum_swap rows columns _
    _ = _ := by
      apply finiteSum_congr
      intro j
      let scale : AddMap Rat Rat := ⟨fun x => x * value j, by grind, by intro a b; grind⟩
      symm
      calc
        _ = finiteSum (fun i => (test i * matrix i j) * value j) rows := finiteSum_map scale _ rows
        _ = _ := finiteSum_congr (fun i => Rat.mul_assoc (test i) (matrix i j) (value j)) rows

def finiteEndpointMass {P S W : Type _} [DecidableEq S] [Abelian W]
    (paths : List P) (terminal : P → S) (weight : P → W) (point : S) : W :=
  finiteSum (fun path => if terminal path = point then weight path else 0) paths

theorem finite_endpoint_pairing {P S W V : Type _} [DecidableEq S] [Abelian W] [Abelian V]
    (paths : List P) (points : List S) (terminal : P → S) (weight : P → W)
    (test : S → AddMap W V) (distinct : points.Nodup)
    (covered : ∀ path ∈ paths, terminal path ∈ points) :
    finiteSum (fun s => test s (finiteEndpointMass paths terminal weight s)) points =
      finiteSum (fun path => test (terminal path) (weight path)) paths := by
  let value (path : P) (point : S) : V :=
    if terminal path = point then test point (weight path) else 0
  calc
    _ = finiteSum (fun s => finiteSum (fun path => value path s) paths) points := by
      apply finiteSum_congr
      intro s
      unfold finiteEndpointMass
      rw [finiteSum_map]
      apply finiteSum_congr
      intro path
      by_cases equal : terminal path = s <;> simp [value, equal]
    _ = finiteSum (fun path => finiteSum (value path) points) paths :=
      finite_sum_swap points paths _
    _ = _ := by
      apply finiteSum_congr_members
      intro path member
      have alone := finiteSum_single_of_nodup (value path) distinct (covered path member)
        (fun s _ other => by simp [value, Ne.symm other])
      rw [alone]
      simp [value]

private def weightOn {W : Type _} [Abelian W] (accepted : Prop) [Decidable accepted] :
    AddMap W W where
  toFun mass := if accepted then mass else 0
  zero := by by_cases h : accepted <;> simp [h]
  add x y := by by_cases h : accepted <;> simp [h]

theorem finite_endpoint_gate_mass {P S W : Type _} [DecidableEq S] [Abelian W]
    (paths : List P) (points : List S) (terminal : P → S) (weight : P → W) (passes : S → Bool)
    (distinct : points.Nodup) (covered : ∀ path ∈ paths, terminal path ∈ points)
    (accepted : ∀ path ∈ paths, weight path ≠ 0 → passes (terminal path) = true) :
    finiteSum (fun s => if passes s then finiteEndpointMass paths terminal weight s else 0) points =
      finiteSum weight paths := by
  calc
    _ = finiteSum (fun path => if passes (terminal path) then weight path else 0) paths :=
      finite_endpoint_pairing paths points terminal weight
        (fun s => weightOn (passes s = true)) distinct covered
    _ = _ := by
      apply finiteSum_congr_members
      intro path member
      by_cases zero : weight path = 0
      · simp [zero]
      · simp [accepted path member zero]

theorem finite_endpoint_mass_coarsen {P S Q W : Type _}
    [DecidableEq S] [DecidableEq Q] [Abelian W]
    (paths : List P) (points : List S) (terminal : P → S) (weight : P → W)
    (quotient : S → Q) (point : Q) (distinct : points.Nodup)
    (covered : ∀ path ∈ paths, terminal path ∈ points) :
    finiteEndpointMass points quotient (finiteEndpointMass paths terminal weight) point =
      finiteEndpointMass paths (fun path => quotient (terminal path)) weight point :=
  finite_endpoint_pairing paths points terminal weight
    (fun s => weightOn (quotient s = point)) distinct covered

open Lean.Grind Std in
def gatedCost {P R : Type _} [Semiring R] (passes : P → Bool) (cost : P → R) (path : P) : R :=
  (if passes path then 0 else 2) + cost path

open Lean.Grind Std in
theorem gated_cost_minimizer {P R : Type _} [Ring R] [LE R] [LT R]
    [IsLinearOrder R] [LawfulOrderLT R] [OrderedRing R]
    (paths : List P) (passes : P → Bool) (cost : P → R)
    (bounds : ∀ path ∈ paths, 0 ≤ cost path ∧ cost path < 1)
    {chosen : P} (member : chosen ∈ paths)
    (minimum : ∀ path ∈ paths, gatedCost passes cost chosen ≤ gatedCost passes cost path)
    (feasible : ∃ path ∈ paths, passes path = true) :
    passes chosen = true ∧ ∀ path ∈ paths, passes path = true → cost chosen ≤ cost path := by
  obtain ⟨alternative, occurs, valid⟩ := feasible
  have pass : passes chosen = true := by
    by_cases selected : passes chosen = true
    · exact selected
    · have comparison := minimum alternative occurs
      have lower := (bounds chosen member).1
      have upper := (bounds alternative occurs).2
      have unit := OrderedRing.zero_lt_one (R := R)
      simp only [gatedCost, ite_eq_right selected, ite_eq_left valid, AddCommMonoid.zero_add] at comparison
      grind
  refine ⟨pass, ?_⟩
  intro path pathMember pathPasses
  simpa only [gatedCost, ite_eq_left pass, ite_eq_left pathPasses, AddCommMonoid.zero_add]
    using minimum path pathMember

end GAlgebra
