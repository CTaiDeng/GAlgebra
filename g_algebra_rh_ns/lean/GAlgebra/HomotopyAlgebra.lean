import GAlgebra.Operators

set_option autoImplicit false
namespace GAlgebra

namespace Bilinear
variable {X : Type _} [Abelian X]

@[simp] theorem zeroLeft (B : Bilinear X X X) (x : X) : B.eval 0 x = 0 :=
  (B.left x).map_zero

@[simp] theorem zeroRight (B : Bilinear X X X) (x : X) : B.eval x 0 = 0 := by
  simp only [eval, B.agreement, AddMap.map_zero]

end Bilinear

section TwoTerm

variable {X : Type _} [Abelian X]

def twoTermD (u : X × X) : X × X := (u.2, 0)

def twoTermB (B : Bilinear X X X) (u v : X × X) : X × X :=
  (B.eval u.1 v.1, B.eval u.1 v.2 + B.eval u.2 v.1)

def twoTermH (B : Bilinear X X X) (u v w : X × X) : X × X :=
  (0, -jacobiDefect B u.1 v.1 w.1)

def pairAdd (u v : X × X) : X × X := (u.1 + v.1, u.2 + v.2)

theorem twoTerm_differential_square (u : X × X) : twoTermD (twoTermD u) = (0, 0) := rfl

theorem twoTerm_signed_leibniz (B : Bilinear X X X) (u v : X × X) :
    twoTermD (twoTermB B u v) =
      pairAdd (twoTermB B (twoTermD u) v) (twoTermB B (u.1, -u.2) (twoTermD v)) := by
  apply Prod.ext <;> simp [twoTermD, twoTermB, pairAdd, B.negLeft]
  exact Abelian.comm _ _

theorem twoTerm_arity_three_zero (B : Bilinear X X X) (x y z : X) :
    jacobiDefect B x y z + (twoTermD (twoTermH B (x, 0) (y, 0) (z, 0))).1 = 0 :=
  Abelian.add_neg _

theorem twoTerm_arity_three_one_negative (B : Bilinear X X X) (x y z : X) :
    let u : X × X := (0, x)
    let v : X × X := (y, 0)
    let w : X × X := (z, 0)
    let jac :=
      pairAdd (pairAdd (twoTermB B (twoTermB B u v) w) (twoTermB B (twoTermB B v w) u))
        (twoTermB B (twoTermB B w u) v)
    pairAdd jac (twoTermH B (twoTermD u) v w) = (0, 0) := by
  simp [pairAdd, twoTermB, twoTermH, twoTermD, jacobiDefect]

theorem jacobi_alternating_first_two (B : Bilinear X X X)
    (skew : ∀ x y, B.eval x y = -B.eval y x)
    (x y z : X) : jacobiDefect B y x z = -jacobiDefect B x y z := by
  unfold jacobiDefect
  rw [skew y x, skew x z, skew z y]
  simp only [B.negLeft, Abelian.neg_add_rev]
  ac_rfl

theorem jacobi_four_arity (B : Bilinear X X X)
    (skew : ∀ x y, B.eval x y = -B.eval y x) (x y z w : X) :
    jacobiDefect B (B.eval x y) z w + -jacobiDefect B (B.eval x z) y w +
      jacobiDefect B (B.eval x w) y z + jacobiDefect B (B.eval y z) x w +
      -jacobiDefect B (B.eval y w) x z + jacobiDefect B (B.eval z w) x y =
    B.eval (jacobiDefect B x y z) w + -B.eval (jacobiDefect B x y w) z +
      B.eval (jacobiDefect B x z w) y + -B.eval (jacobiDefect B y z w) x := by
  have reorder (a b c : X) : jacobiDefect B a b c =
      B.eval (B.eval a b) c + B.eval (B.eval b c) a + -B.eval (B.eval a c) b := by
    unfold jacobiDefect
    rw [skew c a, B.negLeft]
  let t := fun a b c d => B.eval (B.eval (B.eval a b) c) d
  let p := B.eval (B.eval z w) (B.eval x y)
  let q := B.eval (B.eval y w) (B.eval x z)
  let r := B.eval (B.eval y z) (B.eval x w)
  simp only [reorder, B.addLeft, B.negLeft, Abelian.neg_add_rev, Abelian.neg_neg]
  rw [skew (B.eval x w) (B.eval y z), skew (B.eval x z) (B.eval y w),
    skew (B.eval x y) (B.eval z w)]
  simp only [Abelian.neg_neg]
  calc
    _ = (t x y z w + t y z x w + -t x z y w) +
        -(t x y w z + t y w x z + -t x w y z) +
        (t x z w y + t z w x y + -t x w z y) +
        -(t y z w x + t z w y x + -t y w z x) +
        (p + -p) + (q + -q) + (r + -r) := by
      dsimp only [t, p, q, r]
      simp only [Abelian.neg_add_rev, Abelian.neg_neg]
      ac_rfl
    _ = _ := by
      simp only [Abelian.add_neg, Abelian.add_zero, Abelian.neg_add_rev, Abelian.neg_neg]
      dsimp only [t]

theorem twoTerm_double_ternary_zero (B : Bilinear X X X) (u v w d e : X × X) :
    twoTermH B (twoTermH B u v w) d e = (0, 0) := by
  simp [twoTermH, jacobiDefect]

theorem higher_arity_truncation {n i j : Nat} (h : 6 ≤ n) (arity : i + j = n + 1) :
    4 ≤ i ∨ 4 ≤ j := by omega

end TwoTerm

instance {A B : Type _} [Abelian A] [Abelian B] : Abelian (A × B) where
  add u v := (u.1 + v.1, u.2 + v.2)
  zero := (0, 0)
  neg u := (-u.1, -u.2)
  assoc a b c := Prod.ext (Abelian.assoc a.1 b.1 c.1) (Abelian.assoc a.2 b.2 c.2)
  comm a b := Prod.ext (Abelian.comm a.1 b.1) (Abelian.comm a.2 b.2)
  zero_add a := Prod.ext (Abelian.zero_add a.1) (Abelian.zero_add a.2)
  add_neg a := Prod.ext (Abelian.add_neg a.1) (Abelian.add_neg a.2)

abbrev Triple := Int × Int × Int

def threeDimBracket (u v : Triple) : Triple :=
  (0, u.1 * v.2.1 - u.2.1 * v.1, u.2.1 * v.2.2 - u.2.2 * v.2.1)

def threeDimBilinear : Bilinear Triple Triple Triple where
  left y := {
    toFun := fun x => threeDimBracket x y
    zero := by
      apply Prod.ext
      · rfl
      · apply Prod.ext <;> change (0 : Int) * _ - 0 * _ = 0 <;> omega
    add := by
      intro a b
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · change (a.1 + b.1) * y.2.1 - (a.2.1 + b.2.1) * y.1 =
            a.1 * y.2.1 - a.2.1 * y.1 + (b.1 * y.2.1 - b.2.1 * y.1)
          grind
        · change (a.2.1 + b.2.1) * y.2.2 - (a.2.2 + b.2.2) * y.2.1 =
            a.2.1 * y.2.2 - a.2.2 * y.2.1 + (b.2.1 * y.2.2 - b.2.2 * y.2.1)
          grind }
  right x := {
    toFun := fun y => threeDimBracket x y
    zero := by
      apply Prod.ext
      · rfl
      · apply Prod.ext <;> change _ * (0 : Int) - _ * 0 = 0 <;> omega
    add := by
      intro a b
      apply Prod.ext
      · rfl
      · apply Prod.ext
        · change x.1 * (a.2.1 + b.2.1) - x.2.1 * (a.1 + b.1) =
            x.1 * a.2.1 - x.2.1 * a.1 + (x.1 * b.2.1 - x.2.1 * b.1)
          grind
        · change x.2.1 * (a.2.2 + b.2.2) - x.2.2 * (a.2.1 + b.2.1) =
            x.2.1 * a.2.2 - x.2.2 * a.2.1 + (x.2.1 * b.2.2 - x.2.2 * b.2.1)
          grind }
  agreement _ _ := rfl

theorem threeDim_skew (x y : Triple) :
    threeDimBilinear.eval x y = -threeDimBilinear.eval y x := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · change x.1 * y.2.1 - x.2.1 * y.1 = -(y.1 * x.2.1 - y.2.1 * x.1)
      grind
    · change x.2.1 * y.2.2 - x.2.2 * y.2.1 =
        -(y.2.1 * x.2.2 - y.2.2 * x.2.1)
      grind

theorem threeDim_jacobi_nonzero :
    jacobiDefect threeDimBilinear (1, 0, 0) (0, 1, 0) (0, 0, 1) = (0, 0, 1) ∧
      jacobiDefect threeDimBilinear (1, 0, 0) (0, 1, 0) (0, 0, 1) ≠ 0 := by decide

end GAlgebra
