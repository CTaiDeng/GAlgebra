import GAlgebra.Core

set_option autoImplicit false
namespace GAlgebra

structure RationalInterval where
  lower : Rat
  upper : Rat

def RationalInterval.contains (I : RationalInterval) (x : Rat) : Prop :=
  I.lower ≤ x ∧ x ≤ I.upper

/-- Nested rational enclosures whose widths approach zero. -/
structure IntervalSequence where
  bounds : Nat → RationalInterval
  valid : ∀ n, (bounds n).lower ≤ (bounds n).upper
  lower_mono : ∀ n m, n ≤ m → (bounds n).lower ≤ (bounds m).lower
  upper_anti : ∀ n m, n ≤ m → (bounds m).upper ≤ (bounds n).upper
  precise : ∀ ε : Rat, 0 < ε → ∃ n, (bounds n).upper - (bounds n).lower < ε

namespace IntervalSequence

def point (value : Rat) : IntervalSequence where
  bounds _ := ⟨value, value⟩
  valid _ := by grind
  lower_mono _ _ _ := by grind
  upper_anti _ _ _ := by grind
  precise _ positive := ⟨0, by grind⟩

def add (x y : IntervalSequence) : IntervalSequence where
  bounds n := ⟨(x.bounds n).lower + (y.bounds n).lower,
    (x.bounds n).upper + (y.bounds n).upper⟩
  valid n := by
    have hx := x.valid n
    have hy := y.valid n
    grind
  lower_mono n m h := by
    have hx := x.lower_mono n m h
    have hy := y.lower_mono n m h
    grind
  upper_anti n m h := by
    have hx := x.upper_anti n m h
    have hy := y.upper_anti n m h
    grind
  precise ε positive := by
    have half : 0 < ε / 2 := by grind
    obtain ⟨n, xNarrow⟩ := x.precise (ε / 2) half
    obtain ⟨m, yNarrow⟩ := y.precise (ε / 2) half
    let k := max n m
    have xl := x.lower_mono n k (Nat.le_max_left n m)
    have xu := x.upper_anti n k (Nat.le_max_left n m)
    have yl := y.lower_mono m k (Nat.le_max_right n m)
    have yu := y.upper_anti m k (Nat.le_max_right n m)
    exact ⟨k, by grind⟩

end IntervalSequence
end GAlgebra
