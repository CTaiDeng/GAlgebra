import GAlgebra.Core

set_option autoImplicit false
namespace GAlgebra

structure Task (X A O : Type _) where
  act : A → X → X
  observe : X → O

def totalAction {X A : Type _} (act : A → X → Option X) (a : A) : Option X → Option X
  | none => none
  | some x => act a x

theorem failure_absorbs {X A : Type _} (act : A → X → Option X) (a : A) :
    totalAction act a none = none := rfl

class FiberGroup (K : Type _) extends Mul K, Inv K, OfNat K 1 where
  assoc : ∀ a b c : K, (a * b) * c = a * (b * c)
  one_mul : ∀ a : K, 1 * a = a
  mul_one : ∀ a : K, a * 1 = a
  inv_mul : ∀ a : K, a⁻¹ * a = 1
  mul_inv : ∀ a : K, a * a⁻¹ = 1

def fiberRight {L K : Type _} [FiberGroup K] (point : L × K) (h : K) : L × K :=
  (point.1, point.2 * h)

def fiberTransport {L K : Type _} [FiberGroup K] (target : L) (k : K) (point : L × K) :
    L × K :=
  (target, k * point.2)

theorem fiber_right_action {L K : Type _} [FiberGroup K] (point : L × K) (h k : K) :
    fiberRight point 1 = point ∧ fiberRight (fiberRight point h) k = fiberRight point (h * k) := by
  rcases point with ⟨base, g⟩
  simp [fiberRight, FiberGroup.mul_one, FiberGroup.assoc]

theorem fiber_right_unique {L K : Type _} [FiberGroup K] (base : L) (g target h : K) :
    fiberRight (base, g) h = (base, target) ↔ h = g⁻¹ * target := by
  constructor
  · intro equal
    have same := congrArg Prod.snd equal
    change g * h = target at same
    rw [← same, ← FiberGroup.assoc, FiberGroup.inv_mul, FiberGroup.one_mul]
  · intro equal
    simp [fiberRight, equal, ← FiberGroup.assoc, FiberGroup.mul_inv, FiberGroup.one_mul]

theorem fiber_transport_equivariant {L K : Type _} [FiberGroup K]
    (target : L) (k h : K) (point : L × K) :
    fiberTransport target k (fiberRight point h) = fiberRight (fiberTransport target k point) h := by
  simp [fiberTransport, fiberRight, FiberGroup.assoc]

theorem fiber_transport_comp {L K : Type _} [FiberGroup K] (middle target : L)
    (a b : K) (point : L × K) :
    fiberTransport target b (fiberTransport middle a point) = fiberTransport target (b * a) point := by
  simp [fiberTransport, FiberGroup.assoc]

theorem fiber_transport_defect_zero {L K : Type _} [FiberGroup K]
    (origin target : L) (positive negative : K) :
    negative⁻¹ * positive = 1 ↔
      ∀ g : K, fiberTransport target positive (origin, g) = fiberTransport target negative (origin, g) := by
  constructor
  · intro zero g
    have same : positive = negative := by
      have multiplied := congrArg (fun k => negative * k) zero
      simpa only [← FiberGroup.assoc, FiberGroup.mul_inv, FiberGroup.one_mul,
        FiberGroup.mul_one] using multiplied
    rw [same]
  · intro same
    have equal := congrArg Prod.snd (same 1)
    change positive * 1 = negative * 1 at equal
    simp only [FiberGroup.mul_one] at equal
    rw [equal, FiberGroup.inv_mul]

namespace Task

variable {X Y Z A O : Type _}

def run (M : Task X A O) : List A → X → X
  | [], x => x
  | a :: w, x => M.run w (M.act a x)

theorem run_append (M : Task X A O) (u v : List A) (x : X) :
    M.run (u ++ v) x = M.run v (M.run u x) := by
  induction u generalizing x with
  | nil => rfl
  | cons a u ih => exact ih (M.act a x)

def signature (M : Task X A O) (x : X) (w : List A) : O := M.observe (M.run w x)

def EquivBeh (M : Task X A O) (x y : X) : Prop := ∀ w, M.signature x w = M.signature y w

def behaviour (M : Task X A O) : Setoid X where
  r := M.EquivBeh
  iseqv := ⟨fun _ _ => rfl, fun h w => (h w).symm, fun h k w => (h w).trans (k w)⟩

def encode (M : Task X A O) (x : X) : Quotient M.behaviour := Quotient.mk _ x

theorem encode_eq_iff (M : Task X A O) (x y : X) :
    M.encode x = M.encode y ↔ M.EquivBeh x y :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem encode_surjective (M : Task X A O) (q : Quotient M.behaviour) :
    ∃ x, M.encode x = q := by
  induction q using Quotient.ind with
  | _ x => exact ⟨x, rfl⟩

theorem behaviour_congruence (M : Task X A O) (a : A) {x y : X} (h : M.EquivBeh x y) :
    M.EquivBeh (M.act a x) (M.act a y) :=
  fun w => h (a :: w)

def quotient (M : Task X A O) : Task (Quotient M.behaviour) A O where
  act a := Quotient.lift (fun x => M.encode (M.act a x))
    (fun _ _ h => (M.encode_eq_iff _ _).mpr (M.behaviour_congruence a h))
  observe := Quotient.lift M.observe fun _ _ h => h []

structure Exact (M : Task X A O) (N : Task Y A O) (p : X → Y) : Prop where
  step : ∀ a x, p (M.act a x) = N.act a (p x)
  read : ∀ x, M.observe x = N.observe (p x)

theorem encode_exact (M : Task X A O) : M.Exact M.quotient M.encode :=
  ⟨fun _ _ => rfl, fun _ => rfl⟩

theorem Exact.run {M : Task X A O} {N : Task Y A O} {p : X → Y}
    (h : M.Exact N p) (w : List A) (x : X) : p (M.run w x) = N.run w (p x) := by
  induction w generalizing x with
  | nil => rfl
  | cons a w ih =>
    change p (M.run w (M.act a x)) = N.run w (N.act a (p x))
    rw [ih, h.step]

theorem Exact.signature {M : Task X A O} {N : Task Y A O} {p : X → Y}
    (h : M.Exact N p) (w : List A) (x : X) : M.signature x w = N.signature (p x) w := by
  unfold Task.signature
  rw [h.read, h.run]

theorem active_coordinate_projection {I Value : Type _}
    (M : Task (I → Value) A O) (keep : I → Prop) [DecidablePred keep] (fallback : I → Value)
    (reads : ∀ {x y}, (∀ i, keep i → x i = y i) → M.observe x = M.observe y)
    (updates : ∀ a {x y}, (∀ i, keep i → x i = y i) →
      ∀ i, keep i → M.act a x i = M.act a y i) :
    ∃ N : Task ({i : I // keep i} → Value) A O, M.Exact N (fun x i => x i.val) := by
  let extend (active : {i : I // keep i} → Value) (i : I) : Value :=
    if present : keep i then active ⟨i, present⟩ else fallback i
  have agrees (state : I → Value) : ∀ i, keep i →
      state i = extend (fun j => state j.val) i := by
    intro i present
    simp [extend, present]
  refine ⟨{
    act := fun a active i => M.act a (extend active) i.val
    observe := fun active => M.observe (extend active)
  }, ⟨?_, ?_⟩⟩
  · intro a state
    funext i
    exact updates a (agrees state) i.val i.property
  · intro state
    exact reads (agrees state)

theorem Exact.comp {M : Task X A O} {N : Task Y A O} {P : Task Z A O}
    {p : X → Y} {q : Y → Z} (hp : M.Exact N p) (hq : N.Exact P q) :
    M.Exact P (q ∘ p) := by
  exact ⟨fun a x => (congrArg q (hp.step a x)).trans (hq.step a (p x)),
    fun x => (hp.read x).trans (hq.read (p x))⟩

theorem law_information_necessary {M : Task X A O} {N : Task Y A O} {p : X → Y}
    (h : M.Exact N p) {x y : X} {w : List A} (different : M.signature x w ≠ M.signature y w) :
    p x ≠ p y := by
  intro e
  apply different
  rw [h.signature w x, h.signature w y, e]

noncomputable def factor (M : Task X A O) (p : X → Y)
    (onto : ∀ y, ∃ x, p x = y) (y : Y) : Quotient M.behaviour :=
  M.encode (Classical.choose (onto y))

theorem factor_on_image {M : Task X A O} {N : Task Y A O} {p : X → Y}
    (h : M.Exact N p) (onto : ∀ y, ∃ x, p x = y) (x : X) :
    M.factor p onto (p x) = M.encode x := by
  apply (M.encode_eq_iff _ _).mpr
  intro w
  rw [h.signature, h.signature w x, Classical.choose_spec (onto (p x))]

theorem coarsest_task_quotient {M : Task X A O} {N : Task Y A O} (p : X → Y)
    (h : M.Exact N p) (onto : ∀ y, ∃ x, p x = y) :
    ∃ r : Y → Quotient M.behaviour,
      N.Exact M.quotient r ∧ (∀ x, r (p x) = M.encode x) ∧
      (∀ q, ∃ y, r y = q) ∧
      (∀ s : Y → Quotient M.behaviour, (∀ x, s (p x) = M.encode x) → s = r) := by
  let r := M.factor p onto
  have hr : ∀ x, r (p x) = M.encode x := factor_on_image h onto
  refine ⟨r, ⟨?_, ?_⟩, hr, ?_, ?_⟩
  · intro a y
    obtain ⟨x, rfl⟩ := onto y
    rw [← h.step, hr, hr]
    exact (M.encode_exact.step a x)
  · intro y
    obtain ⟨x, rfl⟩ := onto y
    rw [hr, ← h.read x]
    rfl
  · intro q
    obtain ⟨x, rfl⟩ := M.encode_surjective q
    exact ⟨p x, hr x⟩
  · intro s hs
    funext y
    obtain ⟨x, rfl⟩ := onto y
    exact (hs x).trans (hr x).symm

theorem reduced_exact_is_bijective {M : Task X A O} {N : Task Y A O} (p : X → Y)
    (h : M.Exact N p) (onto : ∀ y, ∃ x, p x = y)
    (reduced : ∀ x y, M.EquivBeh x y → p x = p y) :
    (∀ y z, M.factor p onto y = M.factor p onto z → y = z) ∧
      (∀ q, ∃ y, M.factor p onto y = q) := by
  constructor
  · intro y z e
    obtain ⟨x, rfl⟩ := onto y
    obtain ⟨x', rfl⟩ := onto z
    rw [factor_on_image h onto, factor_on_image h onto] at e
    exact reduced _ _ ((M.encode_eq_iff _ _).mp e)
  · intro q
    obtain ⟨x, rfl⟩ := M.encode_surjective q
    exact ⟨p x, factor_on_image h onto x⟩

theorem quotient_differential_necessary (q : X → Y) (p : Z → O) (d : X → Z)
    (d' : Y → O) (h : ∀ x, d' (q x) = p (d x))
    {x y : X} (he : q x = q y) : p (d x) = p (d y) := by
  rw [← h, ← h, he]

theorem quotient_differential_sufficient (q : X → Y) (f : X → O)
    (onto : ∀ y, ∃ x, q x = y) (compatible : ∀ x y, q x = q y → f x = f y) :
    ∃ g : Y → O, (∀ x, g (q x) = f x) ∧
      (∀ g' : Y → O, (∀ x, g' (q x) = f x) → g' = g) := by
  let g := fun y => f (Classical.choose (onto y))
  have hg : ∀ x, g (q x) = f x :=
    fun x => compatible _ _ (Classical.choose_spec (onto (q x)))
  refine ⟨g, hg, ?_⟩
  intro g' h
  funext y
  obtain ⟨x, rfl⟩ := onto y
  exact (h x).trans (hg x).symm

def EquivAt (M : Task X A O) (n : Nat) (x y : X) : Prop :=
  ∀ w : List A, w.length ≤ n → M.signature x w = M.signature y w

theorem finite_refinement_step (M : Task X A O) (n : Nat) (x y : X) :
    M.EquivAt (n + 1) x y ↔
      M.observe x = M.observe y ∧ ∀ a, M.EquivAt n (M.act a x) (M.act a y) := by
  constructor
  · intro h
    refine ⟨h [] (by simp), ?_⟩
    intro a w hw
    exact h (a :: w) (by simpa only [List.length_cons, Nat.add_le_add_iff_right] using hw)
  · rintro ⟨observe, steps⟩ w hw
    cases w with
    | nil => exact observe
    | cons a w =>
      exact steps a w (by simpa only [List.length_cons, Nat.add_le_add_iff_right] using hw)

theorem finite_refinement_fixed (M : Task X A O) (n : Nat)
    (fixed : ∀ x y, M.EquivAt n x y ↔ M.EquivAt (n + 1) x y) (x y : X) :
    M.EquivAt n x y ↔ M.EquivBeh x y := by
  have stable : ∀ k x y, M.EquivAt n x y → M.EquivAt (n + k) x y := by
    intro k
    induction k with
    | zero => exact fun _ _ h => h
    | succ k ih =>
      intro x y h
      obtain ⟨obs, localSteps⟩ := (M.finite_refinement_step n x y).mp ((fixed x y).mp h)
      apply (M.finite_refinement_step (n + k) x y).mpr
      exact ⟨obs, fun a => ih _ _ (localSteps a)⟩
  exact ⟨fun h w => stable w.length x y h w (by omega), fun h w _ => h w⟩

def lawUnion {L : Type _} {X : L → Type _} (M : ∀ l, Task (X l) A O) :
    Task (Sigma X) A O where
  act a x := ⟨x.1, (M x.1).act a x.2⟩
  observe x := (M x.1).observe x.2

theorem fixed_law_exact {L : Type _} {X : L → Type _} (M : ∀ l, Task (X l) A O) (l : L) :
    (M l).Exact (lawUnion M) (fun x => ⟨l, x⟩) := ⟨fun _ _ => rfl, fun _ => rfl⟩

theorem fixed_law_retract {L : Type _} {X : L → Type _} (l : L) (x : X l) :
    (Sigma.snd (⟨l, x⟩ : Sigma X)) = x := rfl

def lawExample (moving : Bool) : Task (Fin 3) Unit Bool where
  act _ x := if x.val = 0 then 1 else if moving then 2 else x
  observe x := x.val == 2

theorem two_step_law_example :
    (lawUnion lawExample).signature ⟨false, 0⟩ [(), ()] = false ∧
    (lawUnion lawExample).signature ⟨true, 0⟩ [(), ()] = true := by
  exact ⟨rfl, rfl⟩

theorem auxiliary_compression {C A : Type _} (a₀ : A) :
    ∃ put : C → C × A, ∃ get : C × A → C,
      (∀ c, get (put c) = c) ∧ (∀ x, get (put (get x)) = get x) :=
  ⟨fun c => (c, a₀), Prod.fst, fun _ => rfl, fun _ => rfl⟩

theorem ordered_record_readback {X A : Type _} (κ : X → List A → Nat)
    (x y : X) (u v : List A) (h : (x, u, κ x u) = (y, v, κ y v)) :
    x = y ∧ u = v :=
  ⟨congrArg Prod.fst h, congrArg (fun t => t.2.1) h⟩

end Task

theorem finite_strict_refinement_bound (count : Nat → Nat) (n : Nat)
    (cap : ∀ i, count i ≤ n) (inc : ∀ i, count i ≤ count (i + 1)) :
    ∃ i, i ≤ n - count 0 ∧ count (i + 1) = count i := by
  classical
  by_cases h : ∃ i, i ≤ n - count 0 ∧ count (i + 1) = count i
  · exact h
  · have growth : ∀ j, j ≤ n - count 0 + 1 → count 0 + j ≤ count j := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        intro hj
        have h₁ := ih (by omega)
        have h₂ := inc j
        have h₃ : count (j + 1) ≠ count j := fun e => h ⟨j, by omega, e⟩
        omega
    have h' := growth (n - count 0 + 1) (by omega)
    have h₀ := cap 0
    have hn := cap (n - count 0 + 1)
    omega

theorem typed_transport_shared_difference {Source Target : Type _}
    (transport : Source → Target) (sourceTest : Source → Rat) (targetTest : Target → Rat)
    (state : Source) (successor : Target) (step : Rat)
    (preserved : targetTest (transport state) = sourceTest state) :
    (targetTest successor - sourceTest state) / step =
      (targetTest successor - targetTest (transport state)) / step := by
  rw [preserved]

structure SectorStepCost where
  localWork : Rat
  transport : Rat
  verification : Rat
  quotient : Rat

def SectorStepCost.total (edge : SectorStepCost) : Rat :=
  edge.localWork + edge.transport + edge.verification + edge.quotient

theorem sector_path_cost_sum (edges : List SectorStepCost) :
    (edges.map SectorStepCost.total).sum =
      (edges.map SectorStepCost.localWork).sum + (edges.map SectorStepCost.transport).sum +
        (edges.map SectorStepCost.verification).sum + (edges.map SectorStepCost.quotient).sum := by
  induction edges with
  | nil => simp
  | cons edge rest ih =>
    simp only [List.map_cons, List.sum_cons, ih, SectorStepCost.total]
    grind

theorem operator_transport_defect_comp
    {Source Middle Target SourceValue MiddleValue TargetValue : Type _}
    [Abelian SourceValue] [Abelian MiddleValue] [Abelian TargetValue]
    (first : Source → Middle) (next : Middle → Target)
    (sourceOp : Source → SourceValue) (middleOp : Middle → MiddleValue)
    (targetOp : Target → TargetValue)
    (firstRead : AddMap SourceValue MiddleValue) (nextRead : AddMap MiddleValue TargetValue)
    (x : Source) :
    targetOp (next (first x)) + -(nextRead (firstRead (sourceOp x))) =
      (targetOp (next (first x)) + -(nextRead (middleOp (first x)))) +
        nextRead (middleOp (first x) + -(firstRead (sourceOp x))) := by
  rw [nextRead.map_add, nextRead.map_neg]
  rw [Abelian.comm (targetOp (next (first x)) + -(nextRead (middleOp (first x))))]
  exact (Abelian.telescopes _ _ _).symm

theorem operator_transport_rate {X Y U V : Type _} [Abelian U] [Abelian V]
    (move : X → Y) (sourceOp : X → U) (targetOp : Y → V) (read : AddMap U V)
    (divideSource : AddMap U U) (divideTarget : AddMap V V)
    (commutes : ∀ value, divideTarget (read value) = read (divideSource value))
    (x next : X) :
    let defect := fun z => targetOp (move z) + -(read (sourceOp z))
    divideTarget (targetOp (move next) + -(targetOp (move x))) =
      read (divideSource (sourceOp next + -(sourceOp x))) +
        divideTarget (defect next + -(defect x)) := by
  let a := read (sourceOp next)
  let b := read (sourceOp x)
  let c := targetOp (move next)
  let d := targetOp (move x)
  change divideTarget (c + -d) =
    read (divideSource (sourceOp next + -(sourceOp x))) + divideTarget ((c + -a) + -(d + -b))
  have split : (a + -b) + ((c + -a) + -(d + -b)) = c + -d := calc
    _ = ((a + -b) + (c + -a)) + (b + -d) := by
      rw [Abelian.neg_add_rev d (-b), Abelian.neg_neg]
      exact (Abelian.assoc (a + -b) (c + -a) (b + -d)).symm
    _ = (c + -b) + (b + -d) := by rw [Abelian.telescopes b a c]
    _ = _ := by rw [Abelian.comm, Abelian.telescopes d b c]
  rw [← split, divideTarget.map_add, ← read.map_neg, ← read.map_add, commutes]

theorem operator_transport_pairing {X Y U V Test : Type _}
    [Abelian U] [Abelian V] [Abelian Test] (move : X → Y)
    (sourceOp : X → U) (targetOp : Y → V) (read : AddMap U V) (test : AddMap V Test) (x : X)
    (vanishes : targetOp (move x) + -(read (sourceOp x)) = 0) :
    test (targetOp (move x)) = test (read (sourceOp x)) :=
  congrArg test (Abelian.eq_of_difference_zero vanishes)

/-- Recompute a test when an input in its certified support may have changed. -/
def reuseSupportedTest {I Value Result : Type _} (support : List I) (changed : I → Bool)
    (read : List Value → Result) (cached : Result) (next : I → Value) : Result :=
  if support.any changed then read (support.map next) else cached

theorem reuseSupportedTest_correct {I Value Result : Type _} (support : List I)
    (changed : I → Bool) (read : List Value → Result) (cached : Result) (old next : I → Value)
    (stored : cached = read (support.map old))
    (unchanged : ∀ i, changed i = false → old i = next i) :
    reuseSupportedTest support changed read cached next = read (support.map next) := by
  cases affected : support.any changed with
  | true => simp [reuseSupportedTest, affected]
  | false =>
    have same : support.map old = support.map next := List.map_congr_left fun i member =>
      unchanged i (by simpa using List.any_eq_false.mp affected i member)
    simp [reuseSupportedTest, affected, stored, same]

theorem shared_verification_saves_weighted {Job : Type _} (jobs : List Job)
    (recompute : Job → Bool) (cost : Job → Rat) (overhead : Rat) :
    ((jobs.filter recompute).map cost).sum + overhead < (jobs.map cost).sum ↔
      overhead < ((jobs.filter fun job => !recompute job).map cost).sum := by
  have partition (entries : List Job) : (entries.map cost).sum =
      ((entries.filter recompute).map cost).sum +
      ((entries.filter fun job => !recompute job).map cost).sum := by
    induction entries with
    | nil => simp
    | cons job rest ih =>
      cases selected : recompute job <;>
        simp [selected, ih, Rat.add_assoc, Rat.add_left_comm]
  rw [partition jobs]
  grind

end GAlgebra
