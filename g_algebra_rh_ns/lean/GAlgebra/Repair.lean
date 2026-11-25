import GAlgebra.Core

set_option autoImplicit false
namespace GAlgebra

def lhtsPartialJacGap {I : Type _} (before after : I → Rat) (step : Rat) (i : I) : Rat :=
  (after i - before i) / step

def lhtsPressure {I : Type _} (components : List I) (pressure before after : I → Rat)
    (step : Rat) : Rat :=
  -(components.map (fun i => pressure i * lhtsPartialJacGap before after step i)).sum

theorem lhts_partial_credit {I : Type _} (before after : I → Rat) (step : Rat)
    (nonzero : step ≠ 0) (i : I) :
    before i - after i = -(lhtsPartialJacGap before after step i * step) := by
  rw [lhtsPartialJacGap, Rat.div_mul_cancel nonzero]
  grind

theorem lhts_component_chain {I : Type _} (before middle after : I → Rat) (i : I) :
    before i - after i = (before i - middle i) + (middle i - after i) := by grind

def Repairable {U V : Type _} (B : U → V) (K : U → Prop) (target : V) : Prop :=
  ∃ u, K u ∧ B u = target

def repairImage {U V : Type _} (B : U → V) (K : U → Prop) : V → Prop :=
  Repairable B K

theorem repairable_iff_fiber {U V : Type _} (B : U → V) (K : U → Prop) (target : V) :
    Repairable B K target ↔ Nonempty {u : U // K u ∧ B u = target} := by
  exact ⟨fun ⟨u, h⟩ => ⟨⟨u, h⟩⟩, fun ⟨⟨u, h⟩⟩ => ⟨u, h⟩⟩

def block {U W V : Type _} [Add V] (B : U → V) (R : W → V) (p : U × W) : V :=
  B p.1 + R p.2

def sumSet {V : Type _} [Add V] (S T : V → Prop) : V → Prop :=
  fun x => ∃ s, S s ∧ ∃ t, T t ∧ s + t = x

theorem repair_expansion {U W V : Type _} [Add V]
    (B : U → V) (R : W → V) (K : U → Prop) (L : W → Prop) (x : V) :
    repairImage (block B R) (fun p => K p.1 ∧ L p.2) x ↔
      sumSet (repairImage B K) (repairImage R L) x := by
  constructor
  · rintro ⟨⟨u, w⟩, ⟨hu, hw⟩, he⟩
    exact ⟨B u, ⟨u, hu, rfl⟩, R w, ⟨w, hw, rfl⟩, he⟩
  · rintro ⟨s, ⟨u, hu, rfl⟩, t, ⟨w, hw, rfl⟩, he⟩
    exact ⟨(u, w), ⟨hu, hw⟩, he⟩

theorem repair_expansion_preserves_old {U W V : Type _} [Abelian V] [Zero W]
    (B : U → V) (R : W → V) (K : U → Prop) (L : W → Prop)
    (h0 : L 0) (hR : R 0 = 0) {x : V} :
    Repairable B K x → Repairable (block B R) (fun p => K p.1 ∧ L p.2) x := by
  rintro ⟨u, hu, rfl⟩
  exact ⟨(u, 0), ⟨hu, h0⟩, by simp [block, hR]⟩

theorem repair_expansion_closed {U W V Z : Type _} [Abelian V] [Abelian Z]
    (B : U → V) (R : W → V) (D : AddMap V Z)
    (hB : ∀ u, D (B u) = 0) (hR : ∀ w, D (R w) = 0) (p : U × W) :
    D (block B R p) = 0 := by
  simp [block, hB, hR]

structure RepairMorphism {U V U' V' : Type _} (B : U → V) (K : U → Prop)
    (B' : U' → V') (K' : U' → Prop) where
  onInput : U → U'
  onTarget : V → V'
  square : ∀ u, B' (onInput u) = onTarget (B u)
  legal : ∀ u, K u → K' (onInput u)

theorem RepairMorphism.transport {U V U' V' : Type _} {B : U → V} {K : U → Prop}
    {B' : U' → V'} {K' : U' → Prop} (F : RepairMorphism B K B' K')
    {x : V} {y : V'} (h : F.onTarget x = y) :
    Repairable B K x → Repairable B' K' y := by
  rintro ⟨u, hu, he⟩
  refine ⟨F.onInput u, F.legal u hu, ?_⟩
  rw [F.square, he, h]

theorem repair_transport_iff {U V U' V' : Type _} {B : U → V} {K : U → Prop}
    {B' : U' → V'} {K' : U' → Prop} (F : RepairMorphism B K B' K')
    (G : RepairMorphism B' K' B K) {x : V} {y : V'}
    (hF : F.onTarget x = y) (hG : G.onTarget y = x) :
    Repairable B K x ↔ Repairable B' K' y :=
  ⟨F.transport hF, G.transport hG⟩

theorem repair_transport_family {ι : Type _} {U V U' V' : ι → Type _}
    {B : ∀ i, U i → V i} {K : ∀ i, U i → Prop}
    {B' : ∀ i, U' i → V' i} {K' : ∀ i, U' i → Prop}
    (F : ∀ i, RepairMorphism (B i) (K i) (B' i) (K' i))
    (G : ∀ i, RepairMorphism (B' i) (K' i) (B i) (K i))
    {x : ∀ i, V i} {y : ∀ i, V' i}
    (hF : ∀ i, (F i).onTarget (x i) = y i) (hG : ∀ i, (G i).onTarget (y i) = x i) :
    (∀ i, Repairable (B i) (K i) (x i)) ↔ (∀ i, Repairable (B' i) (K' i) (y i)) :=
  ⟨fun h i => (repair_transport_iff (F i) (G i) (hF i) (hG i)).mp (h i),
   fun h i => (repair_transport_iff (F i) (G i) (hF i) (hG i)).mpr (h i)⟩

theorem synchronized_construction {X Z : Type _} (D : Nat → Z → X)
    (T : Nat → X → X) (T' : Nat → Z → Z) (x : Nat → X) (z : Nat → Z)
    (legal : Nat → Z → Prop) (hx : ∀ n, x (n + 1) = T n (x n))
    (hz : ∀ n, z (n + 1) = T' n (z n))
    (h0 : D 0 (z 0) = x 0) (hl0 : legal 0 (z 0))
    (square : ∀ n a, legal n a → D (n + 1) (T' n a) = T n (D n a))
    (preserves : ∀ n a, legal n a → legal (n + 1) (T' n a)) :
    ∀ n, D n (z n) = x n ∧ legal n (z n) := by
  intro n
  induction n with
  | zero => exact ⟨h0, hl0⟩
  | succ n ih =>
    rw [hx, hz]
    exact ⟨(square n (z n) ih.2).trans (congrArg (T n) ih.1), preserves n (z n) ih.2⟩

theorem parity_obstruction (x : Int) :
    Repairable (fun u : Int => 2 * u) (fun _ => True) x ↔ x % 2 = 0 := by
  constructor
  · rintro ⟨u, _, h⟩
    change 2 * u = x at h
    omega
  · intro h
    exact ⟨x / 2, trivial, by change 2 * (x / 2) = x; omega⟩

theorem integer_expansion :
    ¬ Repairable (fun u : Int => 2 * u) (fun _ => True) 1 ∧
    ∀ x : Int, Repairable (block (fun u : Int => 2 * u) (fun w : Int => w))
      (fun _ => True) x := by
  refine ⟨fun h => by have := (parity_obstruction 1).mp h; omega, ?_⟩
  intro x
  exact ⟨(0, x), trivial, Int.zero_add x⟩

theorem ordered_expansion :
    ¬ Repairable (fun u : Rat => u) (fun u => 0 ≤ u) (-1) ∧
    ∀ x : Rat, Repairable (block (fun u : Rat => u) (fun w : Rat => -w))
      (fun p => 0 ≤ p.1 ∧ 0 ≤ p.2) x := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact (by decide : ¬ (0 : Rat) ≤ -1) hu
  · intro x
    by_cases hx : 0 ≤ x
    · exact ⟨(x, 0), ⟨hx, by change (0 : Rat) ≤ 0; decide⟩,
        by change x + -(0 : Rat) = x; grind⟩
    · exact ⟨(0, -x), ⟨by change (0 : Rat) ≤ 0; decide, by grind⟩,
        by change 0 + -(-x) = x; grind⟩

theorem strict_coefficients_can_lose_old :
    Repairable (fun u : Int => u) (fun u => u = 0) 0 ∧
    ¬ Repairable (block (fun u : Int => u) (fun w : Int => w))
      (fun p => p.1 = 0 ∧ 0 < p.2) 0 := by
  refine ⟨⟨0, rfl, rfl⟩, ?_⟩
  rintro ⟨⟨u, w⟩, ⟨hu, hw⟩, he⟩
  change u + w = 0 at he
  omega

theorem finite_feasibility_not_uniform :
    (∀ n : Nat, ∃ u : Nat, u = n + 1) ∧
    ¬ ∃ M : Nat, ∀ n : Nat, ∃ u, u = n + 1 ∧ u ≤ M := by
  refine ⟨fun n => ⟨n + 1, rfl⟩, ?_⟩
  rintro ⟨M, h⟩
  obtain ⟨u, hu, hb⟩ := h M
  omega

def det2 (u v : Rat × Rat) : Rat := u.1 * v.2 - u.2 * v.1

def stressCombine (u v : Rat × Rat) (a b : Rat) : Rat × Rat :=
  (a * u.1 + b * v.1, a * u.2 + b * v.2)

theorem positive_two_direction_certificate (u v t : Rat × Rat) (h : 0 < det2 u v) :
    (∃ a b : Rat, 0 < a ∧ 0 < b ∧ stressCombine u v a b = t) ↔
      0 < det2 t v ∧ 0 < det2 u t := by
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    have ha' : det2 (stressCombine u v a b) v = a * det2 u v := by
      simp only [det2, stressCombine]
      grind
    have hb' : det2 u (stressCombine u v a b) = b * det2 u v := by
      simp only [det2, stressCombine]
      grind
    exact ⟨ha' ▸ Rat.mul_pos ha h, hb' ▸ Rat.mul_pos hb h⟩
  · rintro ⟨a, b⟩
    let x := det2 t v / det2 u v
    let y := det2 u t / det2 u v
    have hx : 0 < x := (Rat.lt_div_iff h).mpr (by simpa using a)
    have hy : 0 < y := (Rat.lt_div_iff h).mpr (by simpa using b)
    have nz : det2 u v ≠ 0 := Rat.ne_of_gt h
    have xd : x * det2 u v = det2 t v := Rat.div_mul_cancel nz
    have yd : y * det2 u v = det2 u t := Rat.div_mul_cancel nz
    refine ⟨x, y, hx, hy, ?_⟩
    apply Prod.ext
    · change x * u.1 + y * v.1 = t.1
      have multiplied : (x * u.1 + y * v.1) * det2 u v = t.1 * det2 u v := by
        calc
          _ = (x * det2 u v) * u.1 + (y * det2 u v) * v.1 := by grind
          _ = t.1 * det2 u v := by rw [xd, yd]; simp only [det2]; grind
      have inv := congrArg (fun a : Rat => a / det2 u v) multiplied
      simpa only [Rat.mul_div_cancel nz] using inv
    · change x * u.2 + y * v.2 = t.2
      have multiplied : (x * u.2 + y * v.2) * det2 u v = t.2 * det2 u v := by
        calc
          _ = (x * det2 u v) * u.2 + (y * det2 u v) * v.2 := by grind
          _ = t.2 * det2 u v := by rw [xd, yd]; simp only [det2]; grind
      have inv := congrArg (fun a : Rat => a / det2 u v) multiplied
      simpa only [Rat.mul_div_cancel nz] using inv


end GAlgebra
