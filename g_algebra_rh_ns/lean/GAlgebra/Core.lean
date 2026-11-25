import Init

set_option autoImplicit false

namespace GAlgebra

class Abelian (A : Type _) extends Add A, Zero A, Neg A where
  assoc : ∀ a b c : A, (a + b) + c = a + (b + c)
  comm : ∀ a b : A, a + b = b + a
  zero_add : ∀ a : A, 0 + a = a
  add_neg : ∀ a : A, a + (-a) = 0

namespace Abelian

variable {A : Type _} [Abelian A]

attribute [simp] zero_add add_neg

@[simp] theorem add_zero (a : A) : a + 0 = a := by
  rw [comm, zero_add]

@[simp] theorem neg_add (a : A) : -a + a = 0 := by
  rw [comm, add_neg]

theorem cancel_left {a b c : A} (h : a + b = a + c) : b = c := by
  have e := congrArg (fun x => -a + x) h
  change -a + (a + b) = -a + (a + c) at e
  simpa only [← assoc, neg_add, zero_add] using e

@[simp] theorem neg_zero : -(0 : A) = 0 := by
  simpa only [zero_add] using (add_neg (0 : A))

theorem neg_add_rev (a b : A) : -(a + b) = -b + -a := by
  apply cancel_left (a := a + b)
  rw [add_neg, assoc, ← assoc b, add_neg, zero_add, add_neg]

@[simp] theorem neg_neg (a : A) : -(-a) = a := by
  apply cancel_left (a := -a)
  rw [add_neg, neg_add]

theorem swap_middle (a b c d : A) : (a + b) + (c + d) = (a + c) + (b + d) := by
  rw [assoc, ← assoc b, comm b c, assoc c, ← assoc]

theorem telescopes (a b c : A) : (b + -a) + (c + -b) = c + -a := by
  rw [swap_middle, comm b c, comm (-a) (-b), assoc, ← assoc b, add_neg, zero_add]

theorem eq_of_difference_zero {x y : A} (h : x + -y = 0) : x = y := by
  have h' := congrArg (fun q => q + y) h
  change (x + -y) + y = 0 + y at h'
  simpa only [assoc, neg_add, add_zero, zero_add] using h'

end Abelian

instance : Abelian Int where
  assoc := Int.add_assoc
  comm := Int.add_comm
  zero_add := Int.zero_add
  add_neg := by omega

instance : Abelian Rat where
  assoc := Rat.add_assoc
  comm := Rat.add_comm
  zero_add := Rat.zero_add
  add_neg := by intro x; grind

structure AddMap (A B : Type _) [Abelian A] [Abelian B] where
  toFun : A → B
  zero : toFun 0 = 0
  add : ∀ x y, toFun (x + y) = toFun x + toFun y

namespace AddMap

variable {A B : Type _} [Abelian A] [Abelian B]

instance : CoeFun (AddMap A B) (fun _ => A → B) := ⟨AddMap.toFun⟩

@[simp] theorem map_zero (f : AddMap A B) : f 0 = 0 := f.zero
@[simp] theorem map_add (f : AddMap A B) (a b : A) : f (a + b) = f a + f b := f.add a b

@[simp] theorem map_neg (f : AddMap A B) (a : A) : f (-a) = -f a := by
  apply Abelian.cancel_left (a := f a)
  rw [← map_add, Abelian.add_neg, map_zero, Abelian.add_neg]

end AddMap

structure Subgroup (A : Type _) [Abelian A] where
  mem : A → Prop
  zero : mem 0
  add : ∀ {x y}, mem x → mem y → mem (x + y)
  neg : ∀ {x}, mem x → mem (-x)

namespace Subgroup

variable {A : Type _} [Abelian A]

def congruence (S : Subgroup A) : Setoid A where
  r x y := S.mem (x + -y)
  iseqv := ⟨
    fun x => by simpa only [Abelian.add_neg] using S.zero,
    fun {x y} h => by
      change S.mem (x + -y) at h
      change S.mem (y + -x)
      simpa only [Abelian.neg_add_rev, Abelian.neg_neg] using S.neg h,
    fun {x y z} h₁ h₂ => by
      change S.mem (x + -y) at h₁
      change S.mem (y + -z) at h₂
      change S.mem (x + -z)
      simpa only [Abelian.assoc, ← Abelian.assoc (-y) y, Abelian.neg_add,
        Abelian.zero_add] using S.add h₁ h₂⟩

def classOf (S : Subgroup A) (x : A) : Quotient S.congruence := Quotient.mk S.congruence x

theorem class_eq_iff (S : Subgroup A) (x y : A) :
    S.classOf x = S.classOf y ↔ S.mem (x + -y) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem representative (S : Subgroup A) (q : Quotient S.congruence) :
    ∃ x, S.classOf x = q := by
  induction q using Quotient.ind with
  | _ x => exact ⟨x, rfl⟩

def kernel {B : Type _} [Abelian B] (f : AddMap A B) : Subgroup A where
  mem a := f a = 0
  zero := f.map_zero
  add := fun hx hy => by simp [hx, hy]
  neg := fun hx => by simp [hx]

def range {B : Type _} [Abelian B] (f : AddMap B A) : Subgroup A where
  mem a := ∃ x, f x = a
  zero := ⟨0, f.map_zero⟩
  add := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, f.map_add x y⟩
  neg := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, f.map_neg x⟩

end Subgroup
end GAlgebra
