import GAlgebra.Core

set_option autoImplicit false
namespace GAlgebra

structure Iso (A B : Type _) where
  forward : A → B
  inverse : B → A
  left_inv : ∀ a, inverse (forward a) = a
  right_inv : ∀ b, forward (inverse b) = b

namespace Subgroup

variable {X Y Z : Type _} [Abelian X] [Abelian Y] [Abelian Z]

theorem quotient_add_classes (S : Subgroup X) {a a' b b' : X}
    (ha : S.classOf a = S.classOf a') (hb : S.classOf b = S.classOf b') :
    S.classOf (a + b) = S.classOf (a' + b') := by
  have h := S.add ((S.class_eq_iff _ _).mp ha) ((S.class_eq_iff _ _).mp hb)
  apply (S.class_eq_iff _ _).mpr
  rw [Abelian.neg_add_rev, Abelian.comm (-b') (-a'), Abelian.swap_middle]
  exact h

theorem quotient_scalar_classes {K : Type _} (S : Subgroup X) (scale : K → X → X)
    (add : ∀ k x y, scale k (x + y) = scale k x + scale k y)
    (neg : ∀ k x, scale k (-x) = -scale k x)
    (stable : ∀ k x, S.mem x → S.mem (scale k x)) (k : K) {a b : X}
    (h : S.classOf a = S.classOf b) :
    S.classOf (scale k a) = S.classOf (scale k b) := by
  apply (S.class_eq_iff _ _).mpr
  simpa only [add, neg] using stable k (a + -b) ((S.class_eq_iff _ _).mp h)

theorem map_from_generators_surj {I : Type _} (f : AddMap X Y) (basis : I → Y)
    (spans : ∀ y, ∃ is : List I,
      is.foldr (fun i acc => basis i + acc) 0 = y)
    (lift : ∀ i, ∃ x, f x = basis i) : ∀ y, ∃ x, f x = y := by
  intro y
  obtain ⟨is, rfl⟩ := spans y
  induction is with
  | nil => exact ⟨0, f.map_zero⟩
  | cons i is ih =>
    obtain ⟨xi, hi⟩ := lift i
    obtain ⟨tail, ht⟩ := ih
    exact ⟨xi + tail, by rw [f.map_add, hi, ht]; rfl⟩

def mapClasses (S : Subgroup X) (T : Subgroup Y) (f : AddMap X Y)
    (hf : ∀ x, S.mem x → T.mem (f x)) :
    Quotient S.congruence → Quotient T.congruence :=
  Quotient.lift (fun x => T.classOf (f x)) fun x y h => by
    apply (T.class_eq_iff _ _).mpr
    simpa only [f.map_add, f.map_neg] using hf (x + -y) h

theorem quotient_diff_closed (S : Subgroup X) (T : Subgroup Y) (U : Subgroup Z)
    (d : AddMap X Y) (e : AddMap Y Z)
    (hd : ∀ x, S.mem x → T.mem (d x)) (he : ∀ y, T.mem y → U.mem (e y))
    (square : ∀ x, e (d x) = 0) (q : Quotient S.congruence) :
    T.mapClasses U e he (S.mapClasses T d hd q) = U.classOf 0 := by
  induction q using Quotient.ind with
  | _ x =>
    change U.classOf (e (d x)) = U.classOf 0
    rw [square]

theorem quotient_square_mod (S : Subgroup X) (T : Subgroup Y) (U : Subgroup Z)
    (f g : AddMap X Y) (j k : AddMap Y Z)
    (hf : ∀ x, S.mem x → T.mem (f x)) (hg : ∀ x, S.mem x → T.mem (g x))
    (hj : ∀ y, T.mem y → U.mem (j y)) (hk : ∀ y, T.mem y → U.mem (k y))
    (h : ∀ x, U.mem (j (f x) + -k (g x))) (q : Quotient S.congruence) :
    T.mapClasses U j hj (S.mapClasses T f hf q) =
      T.mapClasses U k hk (S.mapClasses T g hg q) := by
  induction q using Quotient.ind with
  | _ x => exact (U.class_eq_iff _ _).mpr (h x)

def quotientBridge (S : Subgroup X) (T : Subgroup Y) (f : AddMap X Y) (g : AddMap Y X)
    (hf : ∀ x, S.mem x → T.mem (f x)) (hg : ∀ y, T.mem y → S.mem (g y))
    (left : ∀ x, S.mem (g (f x) + -x)) (right : ∀ y, T.mem (f (g y) + -y)) :
    Iso (Quotient S.congruence) (Quotient T.congruence) where
  forward := S.mapClasses T f hf
  inverse := T.mapClasses S g hg
  left_inv q := by
    induction q using Quotient.ind with
    | _ x =>
      change S.classOf (g (f x)) = S.classOf x
      exact (S.class_eq_iff _ _).mpr (left x)
  right_inv q := by
    induction q using Quotient.ind with
    | _ y =>
      change T.classOf (f (g y)) = T.classOf y
      exact (T.class_eq_iff _ _).mpr (right y)

def kernelRead (f : AddMap X Y) : Quotient (kernel f).congruence → Y :=
  Quotient.lift f fun x y h => by
    apply Abelian.eq_of_difference_zero
    change f (x + -y) = 0 at h
    simpa only [f.map_add, f.map_neg] using h

theorem kernelRead_injective (f : AddMap X Y) :
    ∀ a b, kernelRead f a = kernelRead f b → a = b := by
  intro a b
  induction a using Quotient.ind with
  | _ x =>
    induction b using Quotient.ind with
    | _ y =>
      intro h
      change f x = f y at h
      apply ((kernel f).class_eq_iff _ _).mpr
      change f (x + -y) = 0
      simp [h]

noncomputable def kernelQuotient (f : AddMap X Y) (onto : ∀ y, ∃ x, f x = y) :
    Iso (Quotient (kernel f).congruence) Y where
  forward := kernelRead f
  inverse y := (kernel f).classOf (Classical.choose (onto y))
  left_inv q := kernelRead_injective f _ _ (Classical.choose_spec (onto (kernelRead f q)))
  right_inv y := Classical.choose_spec (onto y)

theorem kernel_subcomplex (d : AddMap X Y) (d' : AddMap X Z)
    (f : AddMap Y Z) (commute : ∀ x, f (d x) = d' x) :
    ∀ x, (kernel d').mem x → (kernel f).mem (d x) := by
  intro x hx
  exact (commute x).trans hx

def restrictCongruence (S T : Subgroup X) : Setoid {x : X // T.mem x} where
  r x y := S.congruence.r x.val y.val
  iseqv := ⟨fun _ => S.congruence.refl _, fun h => S.congruence.symm h,
    fun h₁ h₂ => S.congruence.trans h₁ h₂⟩

def quotientToLarger (S T : Subgroup X) (sub : ∀ x, S.mem x → T.mem x) :
    Quotient S.congruence → Quotient T.congruence :=
  Quotient.lift T.classOf fun x y h => (T.class_eq_iff x y).mpr (sub (x + -y) h)

theorem class_zero_iff_mem (S : Subgroup X) (x : X) :
    S.classOf x = S.classOf 0 ↔ S.mem x := by
  rw [class_eq_iff, Abelian.neg_zero, Abelian.add_zero]

def QuotientKernel (S T : Subgroup X) (sub : ∀ x, S.mem x → T.mem x) :=
  {q : Quotient S.congruence // S.quotientToLarger T sub q = T.classOf 0}

def extensionKernelMap (S T : Subgroup X) (sub : ∀ x, S.mem x → T.mem x) :
    Quotient (S.restrictCongruence T) → QuotientKernel S T sub :=
  Quotient.lift
    (fun x => ⟨S.classOf x.val, (T.class_zero_iff_mem _).mpr x.property⟩)
    (fun _ _ h => Subtype.ext (Quotient.sound h))

theorem extensionKernelMap_injective (S T : Subgroup X) (sub : ∀ x, S.mem x → T.mem x) :
    ∀ a b, S.extensionKernelMap T sub a = S.extensionKernelMap T sub b → a = b := by
  intro a b
  induction a using Quotient.ind with
  | _ x =>
    induction b using Quotient.ind with
    | _ y =>
      intro h
      have equal : S.classOf x.val = S.classOf y.val :=
        congrArg Subtype.val h
      exact Quotient.sound ((S.class_eq_iff _ _).mp equal)

theorem extensionKernelMap_surjective (S T : Subgroup X) (sub : ∀ x, S.mem x → T.mem x) :
    ∀ q, ∃ a, S.extensionKernelMap T sub a = q := by
  rintro ⟨q, hq⟩
  induction q using Quotient.ind with
  | _ x =>
    have hx : T.mem x := (T.class_zero_iff_mem _).mp hq
    exact ⟨Quotient.mk _ ⟨x, hx⟩, rfl⟩

noncomputable def quotient_extension_kernel (S T : Subgroup X)
    (sub : ∀ x, S.mem x → T.mem x) :
    Iso (Quotient (S.restrictCongruence T)) (QuotientKernel S T sub) where
  forward := S.extensionKernelMap T sub
  inverse y := Classical.choose (S.extensionKernelMap_surjective T sub y)
  left_inv x := S.extensionKernelMap_injective T sub _ _
    (Classical.choose_spec (S.extensionKernelMap_surjective T sub (S.extensionKernelMap T sub x)))
  right_inv y := Classical.choose_spec (S.extensionKernelMap_surjective T sub y)

end Subgroup

structure TwoStep (U V W : Type _) [Abelian U] [Abelian V] [Abelian W] where
  up : AddMap U V
  down : AddMap V W
  square : ∀ u, down (up u) = 0

namespace TwoStep

variable {U V W U' V' W' : Type _}
variable [Abelian U] [Abelian V] [Abelian W] [Abelian U'] [Abelian V'] [Abelian W']

def Cycles (C : TwoStep U V W) := {z : V // C.down z = 0}

def sameClass (C : TwoStep U V W) : Setoid C.Cycles where
  r x y := (Subgroup.range C.up).congruence.r x.val y.val
  iseqv := ⟨fun x => (Subgroup.range C.up).congruence.refl x.val,
    fun h => (Subgroup.range C.up).congruence.symm h,
    fun h k => (Subgroup.range C.up).congruence.trans h k⟩

def H₁ (C : TwoStep U V W) := Quotient C.sameClass

def cycleClass (C : TwoStep U V W) (z : C.Cycles) : C.H₁ := Quotient.mk _ z

def zeroCycle (C : TwoStep U V W) : C.Cycles := ⟨0, C.down.map_zero⟩

theorem boundary_iff_zero_class (C : TwoStep U V W) (z : C.Cycles) :
    C.cycleClass z = C.cycleClass C.zeroCycle ↔ ∃ u, C.up u = z.val := by
  constructor
  · intro h
    have w : ∃ u, C.up u = z.val + -(0 : V) := Quotient.exact h
    simpa only [Abelian.neg_zero, Abelian.add_zero] using w
  · intro h
    apply Quotient.sound
    change ∃ u, C.up u = z.val + -(0 : V)
    simpa only [Abelian.neg_zero, Abelian.add_zero] using h

structure ChainMap (C : TwoStep U V W) (C' : TwoStep U' V' W') where
  high : AddMap U U'
  mid : AddMap V V'
  low : AddMap W W'
  up_square : ∀ u, mid (C.up u) = C'.up (high u)
  down_square : ∀ v, low (C.down v) = C'.down (mid v)

def ChainMap.cycles {C : TwoStep U V W} {C' : TwoStep U' V' W'}
    (f : ChainMap C C') (z : C.Cycles) : C'.Cycles :=
  ⟨f.mid z.val, by rw [← f.down_square, z.property, f.low.map_zero]⟩

def ChainMap.homology {C : TwoStep U V W} {C' : TwoStep U' V' W'}
    (f : ChainMap C C') : C.H₁ → C'.H₁ :=
  Quotient.lift (fun z => C'.cycleClass (f.cycles z)) fun x y h => by
    change ∃ u, C.up u = x.val + -y.val at h
    rcases h with ⟨u, hu⟩
    apply Quotient.sound
    change ∃ u', C'.up u' = f.mid x.val + -f.mid y.val
    exact ⟨f.high u, by rw [← f.up_square, hu, f.mid.map_add, f.mid.map_neg]⟩

def homology_iso {C : TwoStep U V W} {C' : TwoStep U' V' W'}
    (f : ChainMap C C') (g : ChainMap C' C)
    (left : ∀ v, g.mid (f.mid v) = v) (right : ∀ v, f.mid (g.mid v) = v) :
    Iso C.H₁ C'.H₁ where
  forward := f.homology
  inverse := g.homology
  left_inv q := by
    induction q using Quotient.ind with
    | _ z =>
      change C.cycleClass (g.cycles (f.cycles z)) = C.cycleClass z
      exact congrArg C.cycleClass (Subtype.ext (left z.val))
  right_inv q := by
    induction q using Quotient.ind with
    | _ z =>
      change C'.cycleClass (f.cycles (g.cycles z)) = C'.cycleClass z
      exact congrArg C'.cycleClass (Subtype.ext (right z.val))

theorem homotopy_retract_reflects_boundary {C : TwoStep U V W} {C' : TwoStep U' V' W'}
    (j : ChainMap C C') (r : ChainMap C' C)
    (H : AddMap V U) (K : AddMap W V)
    (retract : ∀ v, r.mid (j.mid v) + -v = C.up (H v) + K (C.down v))
    (z : C.Cycles) (w : U') (hw : C'.up w = j.mid z.val) :
    C.up (r.high w + -(H z.val)) = z.val := by
  have hh := retract z.val
  rw [z.property, K.map_zero, Abelian.add_zero, ← hw, r.up_square] at hh
  have e := congrArg (fun t => t + - (C.up (H z.val))) hh
  change (C.up (r.high w) + -z.val) + -C.up (H z.val) =
    C.up (H z.val) + -C.up (H z.val) at e
  have e' : (C.up (r.high w) + -C.up (H z.val)) + -z.val = 0 := by
    rw [Abelian.assoc, Abelian.comm (-C.up (H z.val)), ← Abelian.assoc]
    exact e.trans (Abelian.add_neg _)
  rw [C.up.map_add, C.up.map_neg]
  exact Abelian.eq_of_difference_zero e'

theorem quotient_solution_writeback (C : TwoStep U V W)
    (S : Subgroup V) (h : AddMap V U) (k : AddMap W V)
    (contraction : ∀ r, S.mem r → C.up (h r) + k (C.down r) = r)
    (ω : C.Cycles) (u : U) (qSolution : S.classOf ω.val = S.classOf (C.up u)) :
    C.up (u + h (ω.val + -C.up u)) = ω.val := by
  let residual := ω.val + -C.up u
  have mem : S.mem residual := (S.class_eq_iff _ _).mp qSolution
  have closed : C.down residual = 0 := by
    simp [residual, ω.property, C.square]
  have repair := contraction residual mem
  rw [closed, k.map_zero, Abelian.add_zero] at repair
  rw [C.up.map_add, repair]
  change C.up u + (ω.val + -C.up u) = ω.val
  rw [← Abelian.assoc, Abelian.comm (C.up u) ω.val, Abelian.assoc, Abelian.add_neg,
    Abelian.add_zero]

theorem legal_quotient_solution_writeback (C : TwoStep U V W)
    (S : Subgroup V) (h : AddMap V U) (k : AddMap W V)
    (contraction : ∀ r, S.mem r → C.up (h r) + k (C.down r) = r)
    (ω : C.Cycles) (u : U) (qSolution : S.classOf ω.val = S.classOf (C.up u))
    (legal : U → Prop) (hl : legal (u + h (ω.val + -C.up u))) :
    ∃ z, legal z ∧ C.up z = ω.val :=
  ⟨_, hl, quotient_solution_writeback C S h k contraction ω u qSolution⟩

end TwoStep

end GAlgebra
