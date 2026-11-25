import GAlgebra.Repair

set_option autoImplicit false
namespace GAlgebra

instance {V : Type _} [Abelian V] : Std.Associative (fun x y : V => x + y) :=
  ⟨Abelian.assoc⟩

instance {V : Type _} [Abelian V] : Std.Commutative (fun x y : V => x + y) :=
  ⟨Abelian.comm⟩

structure Bilinear (V W Z : Type _) [Abelian V] [Abelian W] [Abelian Z] where
  left : W → AddMap V Z
  right : V → AddMap W Z
  agreement : ∀ x y, left y x = right x y

namespace Bilinear

variable {V W Z : Type _} [Abelian V] [Abelian W] [Abelian Z]

def eval (B : Bilinear V W Z) (x : V) (y : W) : Z := B.left y x

theorem addLeft (B : Bilinear V W Z) (x y : V) (z : W) :
    B.eval (x + y) z = B.eval x z + B.eval y z :=
  (B.left z).map_add x y

theorem addRight (B : Bilinear V W Z) (x : V) (y z : W) :
    B.eval x (y + z) = B.eval x y + B.eval x z := by
  simp only [eval, B.agreement, AddMap.map_add]

theorem negLeft (B : Bilinear V W Z) (x : V) (y : W) :
    B.eval (-x) y = -B.eval x y :=
  (B.left y).map_neg x

theorem negRight (B : Bilinear V W Z) (x : V) (y : W) :
    B.eval x (-y) = -B.eval x y := by
  simp only [eval, B.agreement, AddMap.map_neg]

end Bilinear

section Operators

variable {X P : Type _} [Abelian X] [Abelian P]

def commutator (B : Bilinear X X X) (x y : X) : X := B.eval x y + -B.eval y x

theorem commutator_alternating (B : Bilinear X X X) (x : X) :
    commutator B x x = 0 := Abelian.add_neg _

theorem commutator_jacobi (B : Bilinear X X X)
    (assoc : ∀ x y z, B.eval (B.eval x y) z = B.eval x (B.eval y z))
    (x y z : X) :
    (commutator B (commutator B x y) z + commutator B (commutator B y z) x) +
      commutator B (commutator B z x) y = 0 := by
  simp only [commutator, B.addLeft, B.addRight, B.negLeft, B.negRight, Abelian.neg_add_rev,
    Abelian.neg_neg, assoc]
  calc
    _ = (B.eval x (B.eval y z) + -B.eval x (B.eval y z)) +
        (B.eval x (B.eval z y) + -B.eval x (B.eval z y)) +
        (B.eval y (B.eval x z) + -B.eval y (B.eval x z)) +
        (B.eval y (B.eval z x) + -B.eval y (B.eval z x)) +
        (B.eval z (B.eval x y) + -B.eval z (B.eval x y)) +
        (B.eval z (B.eval y x) + -B.eval z (B.eval y x)) := by ac_rfl
    _ = 0 := by simp

def jacobiDefect (B : Bilinear X X X) (x y z : X) : X :=
  B.eval (B.eval x y) z + B.eval (B.eval y z) x + B.eval (B.eval z x) y

theorem jacobi_lift_of_section {H : Type _} [Abelian H] (B : Bilinear X X X)
    (d : AddMap H X) (lift : X → H)
    (rightInv : ∀ v, d (lift v) = v) (x y z : X) :
    d (lift (jacobiDefect B x y z)) = jacobiDefect B x y z :=
  rightInv _

def residual (L : AddMap X X) (G : AddMap P X) (B : Bilinear X X X)
    (f u : X) (p : P) : X :=
  L u + G p + B.eval u u + -f

def linearized (L : AddMap X X) (G : AddMap P X) (B : Bilinear X X X)
    (u w : X) (π : P) : X :=
  L w + G π + B.eval u w + B.eval w u

theorem residual_perturbation (L : AddMap X X) (G : AddMap P X) (B : Bilinear X X X)
    (f u w : X) (p π : P) :
    residual L G B f (u + w) (p + π) =
      residual L G B f u p + (linearized L G B u w π + B.eval w w) := by
  simp only [residual, linearized, L.map_add, G.map_add, B.addLeft, B.addRight]
  ac_rfl

theorem convection_cannot_be_alternating (B : Bilinear X X X) (u : X)
    (nonzero : B.eval u u ≠ 0) :
    ¬ ∃ b : X → X → X, (∀ x y, B.eval x y = b x y) ∧ (∀ x, b x x = 0) := by
  rintro ⟨b, hb, h0⟩
  exact nonzero ((hb u u).trans (h0 u))

end Operators

section Compression

open Lean.Grind in
def orderedExpansion {R : Type _} [Semiring R] : List R → R
  | [] => 1
  | a :: as => orderedExpansion as + a * orderedExpansion as

open Lean.Grind in
def factoredExpansion {R : Type _} [Semiring R] : List R → R
  | [] => 1
  | a :: as => (1 + a) * factoredExpansion as

open Lean.Grind in
theorem ordered_product_factorization {R : Type _} [Semiring R] (as : List R) :
    orderedExpansion as = factoredExpansion as := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [orderedExpansion, factoredExpansion, Semiring.right_distrib, Semiring.one_mul, ih]

def selectionWords : List Nat → List (List Nat)
  | [] => [[]]
  | a :: as =>
    let tail := selectionWords as
    tail ++ tail.map (List.cons a)

theorem selection_word_count (as : List Nat) :
    (selectionWords as).length = 2 ^ as.length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [selectionWords, List.length_append, List.length_map, List.length_cons, ih,
      Nat.pow_succ]
    omega

theorem reuse_cost_iff (B K c a : Int) : B + K * c < K * a ↔ B < K * (a - c) := by
  rw [Int.mul_sub]
  omega

end Compression

end GAlgebra
