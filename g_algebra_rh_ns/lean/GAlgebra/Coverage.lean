import GAlgebra.Chain
import GAlgebra.Repair

set_option autoImplicit false
namespace GAlgebra

def finiteSum {I V : Type _} [Abelian V] (f : I → V) : List I → V
  | [] => 0
  | i :: is => f i + finiteSum f is

theorem finiteSum_append {I V : Type _} [Abelian V] (f : I → V) (xs ys : List I) :
    finiteSum f (xs ++ ys) = finiteSum f xs + finiteSum f ys := by
  induction xs with
  | nil => simp only [List.nil_append, finiteSum, Abelian.zero_add]
  | cons i rest ih => simp only [List.cons_append, finiteSum, ih, Abelian.assoc]

theorem finiteSum_congr {I V : Type _} [Abelian V] {f g : I → V}
    (h : ∀ i, f i = g i) (is : List I) : finiteSum f is = finiteSum g is := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [finiteSum, h i, ih]

theorem finiteSum_congr_members {I V : Type _} [Abelian V] (is : List I) {f g : I → V}
    (same : ∀ i ∈ is, f i = g i) : finiteSum f is = finiteSum g is := by
  induction is with
  | nil => rfl
  | cons i rest ih =>
    rw [finiteSum, finiteSum, same i List.mem_cons_self]
    exact congrArg (fun tail => g i + tail)
      (ih (fun j hj => same j (List.mem_cons_of_mem i hj)))

theorem finiteSum_map {I V W : Type _} [Abelian V] [Abelian W] (F : AddMap V W)
    (f : I → V) (is : List I) : F (finiteSum f is) = finiteSum (fun i => F (f i)) is := by
  induction is with
  | nil => exact F.map_zero
  | cons i is ih => simp only [finiteSum, F.map_add, ih]

theorem weighted_gram_factorization {I K V : Type _} {U : I → Type _}
    [Mul K] [Abelian V] (is : List I)
    (B : ∀ i, U i → V) (adj : ∀ i, V → U i)
    (scale : ∀ i, K → U i → U i) (r γ : I → K)
    (mulScale : ∀ i a b x, scale i a (scale i b x) = scale i (a * b) x)
    (weight : ∀ i, r i * r i = γ i) (v : V) :
    finiteSum (fun i => B i (scale i (r i) (scale i (r i) (adj i v)))) is =
      finiteSum (fun i => B i (scale i (γ i) (adj i v))) is := by
  apply finiteSum_congr
  intro i
  rw [mulScale, weight]

theorem weighted_coverage_image {I K V : Type _} {U : I → Type _} [Abelian V]
    (is : List I) (B : ∀ i, U i → V) (scale : ∀ i, K → U i → U i)
    (r : I → K) (undo : ∀ i, U i → U i) (undo_eq : ∀ i x, scale i (r i) (undo i x) = x)
    (v : V) :
    (∃ u : ∀ i, U i, finiteSum (fun i => B i (scale i (r i) (u i))) is = v) ↔
      (∃ u : ∀ i, U i, finiteSum (fun i => B i (u i)) is = v) := by
  constructor
  · rintro ⟨u, h⟩
    exact ⟨fun i => scale i (r i) (u i), h⟩
  · rintro ⟨u, h⟩
    refine ⟨fun i => undo i (u i), ?_⟩
    exact (finiteSum_congr (fun i => congrArg (B i) (undo_eq i (u i))) is).trans h

theorem nonnegative_sum_zero {I K : Type _} [Abelian K] [LE K] (a : I → K)
    (zero : (0 : K) ≤ 0) (plus : ∀ x y : K, 0 ≤ x → 0 ≤ y → 0 ≤ x + y)
    (split : ∀ x y : K, 0 ≤ x → 0 ≤ y → x + y = 0 → x = 0 ∧ y = 0)
    (positive : ∀ i, 0 ≤ a i) (is : List I) :
    0 ≤ finiteSum a is ∧ (finiteSum a is = 0 ↔ ∀ i, i ∈ is → a i = 0) := by
  induction is with
  | nil => simp [finiteSum, zero]
  | cons i is ih =>
    refine ⟨plus _ _ (positive i) ih.1, ?_⟩
    constructor
    · intro h
      have hz := split _ _ (positive i) ih.1 h
      intro j hj
      rcases List.mem_cons.mp hj with h | h
      · exact h ▸ hz.1
      · exact ih.2.mp hz.2 j h
    · intro h
      have hi := h i List.mem_cons_self
      have ht := ih.2.mpr (fun j hj => h j (List.mem_cons_of_mem i hj))
      simp [finiteSum, hi, ht]

structure Pairing (K V : Type _) [Abelian K] [Abelian V] where
  dot : V → V → K
  symmetric : ∀ x y, dot x y = dot y x
  left : V → AddMap V K
  left_eq : ∀ x y, left y x = dot x y
  definite : ∀ x, dot x x = 0 → x = 0

namespace Pairing
variable {K V : Type _} [Abelian K] [Abelian V]

@[simp] theorem zero_left (P : Pairing K V) (x : V) : P.dot 0 x = 0 := by
  rw [← P.left_eq, (P.left x).map_zero]

@[simp] theorem zero_right (P : Pairing K V) (x : V) : P.dot x 0 = 0 := by
  rw [P.symmetric, P.zero_left]

theorem add_left (P : Pairing K V) (x y z : V) :
    P.dot (x + y) z = P.dot x z + P.dot y z := by
  rw [← P.left_eq, (P.left z).map_add, P.left_eq, P.left_eq]

theorem add_right (P : Pairing K V) (x y z : V) :
    P.dot x (y + z) = P.dot x y + P.dot x z := by
  rw [P.symmetric x, P.add_left, P.symmetric y x, P.symmetric z x]

theorem neg_right (P : Pairing K V) (x y : V) :
    P.dot x (-y) = -P.dot x y := by
  rw [P.symmetric x, ← P.left_eq, (P.left x).map_neg, P.left_eq, P.symmetric y x]

def Perp (P : Pairing K V) (S : Subgroup V) (z : V) : Prop :=
  ∀ x, S.mem x → P.dot x z = 0

end Pairing

structure AdjointPair {K U V : Type _} [Abelian K] [Abelian U] [Abelian V]
    (P : Pairing K U) (Q : Pairing K V) where
  forward : AddMap U V
  adjoint : AddMap V U
  adjoint_eq : ∀ u v, Q.dot (forward u) v = P.dot u (adjoint v)

namespace AdjointPair
variable {K U V : Type _} [Abelian K] [Abelian U] [Abelian V]
variable {P : Pairing K U} {Q : Pairing K V}

def gram (B : AdjointPair P Q) (v : V) : V := B.forward (B.adjoint v)

theorem gram_energy (B : AdjointPair P Q) (v : V) :
    Q.dot (B.gram v) v = P.dot (B.adjoint v) (B.adjoint v) :=
  B.adjoint_eq (B.adjoint v) v

theorem gram_kernel (B : AdjointPair P Q) (v : V) :
    B.gram v = 0 ↔ B.adjoint v = 0 := by
  constructor
  · intro h
    apply P.definite
    rw [← B.gram_energy, h, Q.zero_left]
  · intro h
    simp [gram, h]

theorem adjoint_kernel_orthogonal (B : AdjointPair P Q) (v : V) :
    B.adjoint v = 0 ↔ Q.Perp (Subgroup.range B.forward) v := by
  constructor
  · intro h x hx
    change ∃ u, B.forward u = x at hx
    obtain ⟨u, rfl⟩ := hx
    rw [B.adjoint_eq, h, P.zero_right]
  · intro h
    apply P.definite
    rw [← B.gram_energy]
    exact h _ ⟨B.adjoint v, rfl⟩

theorem gram_kernel_orthogonal (B : AdjointPair P Q) (v : V) :
    B.gram v = 0 ↔ Q.Perp (Subgroup.range B.forward) v :=
  (B.gram_kernel v).trans (B.adjoint_kernel_orthogonal v)

end AdjointPair

structure OrthogonalSplitting {K V : Type _} [Abelian K] [Abelian V]
    (P : Pairing K V) (S : Subgroup V) where
  project : AddMap V V
  vanishes : ∀ s, S.mem s → project s = 0
  residual : ∀ x, S.mem (x + -project x)
  lands : ∀ x, P.Perp S (project x)

namespace OrthogonalSplitting

variable {K V : Type _} [Abelian K] [Abelian V]
variable {P : Pairing K V} {S : Subgroup V}

theorem fixes (C : OrthogonalSplitting P S) {v : V} (h : P.Perp S v) :
    C.project v = v := by
  let r := v + -C.project v
  have hm : S.mem r := C.residual v
  have hr : P.dot r r = 0 := by
    change P.dot r (v + -C.project v) = 0
    rw [P.add_right, P.neg_right, h _ hm, C.lands v _ hm]
    simp
  exact (Abelian.eq_of_difference_zero (P.definite r hr)).symm

theorem project_equiv (C : OrthogonalSplitting P S) {x y : V}
    (h : S.mem (x + -y)) : C.project x = C.project y := by
  apply Abelian.eq_of_difference_zero
  simpa only [C.project.map_add, C.project.map_neg] using C.vanishes (x + -y) h

def quotient_orthogonal (C : OrthogonalSplitting P S) :
    Iso (Quotient S.congruence) {v : V // P.Perp S v} where
  forward := Quotient.lift (fun x => ⟨C.project x, C.lands x⟩) fun _ _ h =>
    Subtype.ext (C.project_equiv h)
  inverse v := S.classOf v.val
  left_inv q := by
    induction q using Quotient.ind with
    | _ x =>
      change S.classOf (C.project x) = S.classOf x
      exact ((S.class_eq_iff x (C.project x)).mpr (C.residual x)).symm
  right_inv v := Subtype.ext (C.fixes v.property)

theorem keeps_cycles {W : Type _} [Abelian W] (C : OrthogonalSplitting P S)
    (D : AddMap V W) (onRange : ∀ x, S.mem x → D x = 0) {v : V} (hv : D v = 0) :
    D (C.project v) = 0 := by
  have h := onRange _ (C.residual v)
  rw [D.map_add, D.map_neg, hv, Abelian.zero_add] at h
  have hh := congrArg (fun w : W => -w) h
  simpa only [Abelian.neg_neg, Abelian.neg_zero] using hh

end OrthogonalSplitting

def hodge {K U V W : Type _} [Abelian K] [Abelian U] [Abelian V] [Abelian W]
    {P : Pairing K U} {Q : Pairing K V} {R : Pairing K W}
    (B : AdjointPair P Q) (D : AdjointPair Q R) (v : V) : V :=
  D.adjoint (D.forward v) + B.gram v

theorem hodge_cycle_restrict {K U V W : Type _} [Abelian K] [Abelian U] [Abelian V] [Abelian W]
    {P : Pairing K U} {Q : Pairing K V} {R : Pairing K W}
    (B : AdjointPair P Q) (D : AdjointPair Q R) {v : V} (closed : D.forward v = 0) :
    hodge B D v = B.gram v := by simp [hodge, closed]

theorem hodge_kernel {K U V W : Type _} [Abelian K] [Abelian U] [Abelian V] [Abelian W]
    {P : Pairing K U} {Q : Pairing K V} {R : Pairing K W}
    (B : AdjointPair P Q) (D : AdjointPair Q R)
    (positive : ∀ u w, R.dot w w + P.dot u u = 0 → u = 0 ∧ w = 0)
    (v : V) : hodge B D v = 0 ↔ D.forward v = 0 ∧ B.adjoint v = 0 := by
  constructor
  · intro h
    have energy : Q.dot (hodge B D v) v =
        R.dot (D.forward v) (D.forward v) + P.dot (B.adjoint v) (B.adjoint v) := by
      rw [hodge, Q.add_left, Q.symmetric (D.adjoint (D.forward v)) v, ← D.adjoint_eq,
        B.gram_energy]
    rw [h, Q.zero_left] at energy
    have hz := positive (B.adjoint v) (D.forward v) energy.symm
    exact ⟨hz.2, hz.1⟩
  · rintro ⟨hv, hb⟩
    rw [hodge_cycle_restrict B D hv]
    exact (B.gram_kernel v).mpr hb

def pairedComplex {K U V W : Type _} [Abelian K] [Abelian U] [Abelian V] [Abelian W]
    {P : Pairing K U} {Q : Pairing K V} {R : Pairing K W}
    (B : AdjointPair P Q) (D : AdjointPair Q R)
    (closed : ∀ u, D.forward (B.forward u) = 0) : TwoStep U V W :=
  ⟨B.forward, D.forward, closed⟩

def hodge_homology_iso {K U V W : Type _} [Abelian K] [Abelian U] [Abelian V] [Abelian W]
    {P : Pairing K U} {Q : Pairing K V} {R : Pairing K W}
    (B : AdjointPair P Q) (D : AdjointPair Q R)
    (positive : ∀ u w, R.dot w w + P.dot u u = 0 → u = 0 ∧ w = 0)
    (closed : ∀ u, D.forward (B.forward u) = 0)
    (S : OrthogonalSplitting Q (Subgroup.range B.forward)) :
    Iso (pairedComplex B D closed).H₁ {v : V // hodge B D v = 0} := by
  let C := pairedComplex B D closed
  have downRange : ∀ v, (Subgroup.range B.forward).mem v → D.forward v = 0 := by
    rintro _ ⟨u, rfl⟩
    exact closed u
  have hProject : ∀ z : C.Cycles, hodge B D (S.project z.val) = 0 := by
    intro z
    apply (hodge_kernel B D positive _).mpr
    exact ⟨S.keeps_cycles D.forward downRange z.property,
      (B.adjoint_kernel_orthogonal _).mpr (S.lands z.val)⟩
  let project := fun z : C.Cycles => (⟨S.project z.val, hProject z⟩ : {v : V // hodge B D v = 0})
  let read := fun v : {v : V // hodge B D v = 0} =>
    (⟨v.val, ((hodge_kernel B D positive v.val).mp v.property).1⟩ : C.Cycles)
  let forward : C.H₁ → {v : V // hodge B D v = 0} :=
    Quotient.lift project fun _ _ h => Subtype.ext (S.project_equiv h)
  refine ⟨forward, fun v => C.cycleClass (read v), ?_, ?_⟩
  · intro q
    induction q using Quotient.ind with
    | _ z =>
      change C.cycleClass (read (project z)) = C.cycleClass z
      symm
      apply Quotient.sound
      exact S.residual z.val
  · intro v
    apply Subtype.ext
    change S.project v.val = v.val
    exact S.fixes ((B.adjoint_kernel_orthogonal v.val).mp
      ((hodge_kernel B D positive v.val).mp v.property).2)

theorem rank_gain_count (n old new added : Nat) (coverage : old + added = new) (bound : new ≤ n) :
    (n - old) - (n - new) = added := by omega

theorem quant_lower_bound_scaling {M : Nat} (h : ∀ n : Nat, n + 1 ≤ M) : False := by
  have := h M
  omega

end GAlgebra
