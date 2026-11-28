import GAlgebra.GrandRiemann

set_option autoImplicit false
namespace GAlgebra

open Lean.Grind

/-- Ordinary Taylor coefficients at the common origin in the square-spectrum coordinate. -/
abbrev TaylorSeries (K : Type _) := Nat → K

namespace TaylorSeries

variable {K : Type _} [Field K]
attribute [local instance] Semiring.natCast

private def tail (f : TaylorSeries K) : TaylorSeries K := fun j => f (j + 1)

/-- Cauchy product, with the summand indexed by zero separated from the other summands. -/
def product (f g : TaylorSeries K) (n : Nat) : K :=
  match n with
  | 0 => f 0 * g 0
  | n + 1 => f 0 * g (n + 1) + product (tail f) g n

private theorem product_linear (a : K) (f g h : TaylorSeries K) (n : Nat) :
    product (fun j => a * f j + g j) h n = a * product f h n + product g h n := by
  induction n generalizing f g with
  | zero => simp only [product]; grind
  | succ n ih =>
    simp only [product]
    rw [show tail (fun j => a * f j + g j) = (fun j => a * tail f j + tail g j) from rfl,
      ih (tail f) (tail g)]
    grind

private theorem product_scale (a : K) (f g : TaylorSeries K) (n : Nat) :
    product (fun j => a * f j) g n = a * product f g n := by
  induction n generalizing f with
  | zero => simp only [product]; grind
  | succ n ih =>
    simp only [product]
    rw [show tail (fun j => a * f j) = (fun j => a * tail f j) from rfl, ih (tail f)]
    grind

private theorem product_succ_right (f g : TaylorSeries K) (n : Nat) :
    product f g (n + 1) = product f (tail g) n + f (n + 1) * g 0 := by
  induction n generalizing f with
  | zero => simp only [product, tail]
  | succ n ih =>
    rw [product.eq_2 f g, ih (tail f), product.eq_2 f (tail g)]
    simp only [tail]
    grind

private theorem product_comm (f g : TaylorSeries K) (n : Nat) :
    product f g n = product g f n := by
  induction n generalizing f g with
  | zero => simp only [product]; grind
  | succ n ih =>
    rw [product, product_succ_right g f, ih (tail f) g]
    grind

private theorem product_assoc (f g h : TaylorSeries K) (n : Nat) :
    product (product f g) h n = product f (product g h) n := by
  induction n generalizing f with
  | zero => simp only [product]; grind
  | succ n ih =>
    rw [product.eq_2 (product f g) h, product.eq_2 f (product g h),
      product.eq_2 g h, product.eq_1 f g]
    change _ + product (fun j => f 0 * tail g j + product (tail f) g j) h n = _
    rw [product_linear, ih (tail f)]
    grind

/-- Taylor coefficient of the derivative, in ordinary rather than factorial-scaled derivatives. -/
def deriv (f : TaylorSeries K) (j : Nat) : K := ((j + 1 : Nat) : K) * f (j + 1)

theorem deriv_product (f g : TaylorSeries K) (n : Nat) :
    deriv (product f g) n = product (deriv f) g n + product f (deriv g) n := by
  induction n generalizing f with
  | zero =>
    simp only [deriv, product, tail]
    grind
  | succ n ih =>
    have shifted : tail (deriv f) = fun j => (1 : K) * deriv (tail f) j + tail (tail f) j := by
      funext j
      simp only [tail, deriv, Semiring.natCast_succ]
      grind
    have prev := ih (tail f)
    simp only [deriv] at prev ⊢
    rw [product.eq_2 f g, product.eq_2 (deriv f) g, product.eq_2 f (deriv g)]
    change _ = _ + product (tail (deriv f)) g n + _
    rw [shifted, product_linear]
    have rest := show product (tail f) g (n + 1) =
        tail f 0 * g (n + 1) + product (tail (tail f)) g n from rfl
    simp only [deriv, tail, Semiring.natCast_succ] at *
    grind

/-- Formal division at an ordinary point. Each step removes the leading quotient coefficient. -/
def quotient (num den : TaylorSeries K) (n : Nat) : K :=
  let c := num 0 / den 0
  match n with
  | 0 => c
  | n + 1 => quotient (fun j => num (j + 1) - c * den (j + 1)) den n

private theorem quotient_spec (num den : TaylorSeries K) (unit : den 0 ≠ 0) (n : Nat) :
    product (quotient num den) den n = num n := by
  induction n generalizing num with
  | zero =>
    change num 0 / den 0 * den 0 = num 0
    grind
  | succ n ih =>
    rw [product]
    change num 0 / den 0 * den (n + 1) +
      product (quotient (fun j => num (j + 1) - num 0 / den 0 * den (j + 1)) den) den n = _
    rw [ih]
    grind

private theorem quotient_product (f den : TaylorSeries K) (unit : den 0 ≠ 0) (n : Nat) :
    quotient (product f den) den n = f n := by
  have head : product f den 0 / den 0 = f 0 := by
    change f 0 * den 0 / den 0 = f 0
    grind
  induction n generalizing f with
  | zero => exact head
  | succ n ih =>
    simp only [quotient, head]
    have remainder : (fun j => product f den (j + 1) - f 0 * den (j + 1)) =
        product (tail f) den := by
      funext j
      rw [product]
      grind
    rw [remainder]
    exact ih (tail f) (by change tail f 0 * den 0 / den 0 = tail f 0; grind)

/-- The sign is the one for the coordinate z in D(z) = Y(9/4-z). -/
def resolvent (d : TaylorSeries K) : TaylorSeries K := quotient (fun j => -deriv d j) d

theorem resolvent_square (d : TaylorSeries K) (unit : d 0 ≠ 0) :
    resolvent (product d d) = fun j => 2 * resolvent d j := by
  have squareUnit : product d d 0 ≠ 0 := by
    change d 0 * d 0 ≠ 0
    exact fun h => (Field.of_mul_eq_zero h).elim unit unit
  have numerator : (fun j => -deriv (product d d) j) =
      product (fun j => 2 * resolvent d j) (product d d) := by
    funext j
    rw [deriv_product, product_comm d (deriv d), product_scale, ← product_assoc]
    have row : product (resolvent d) d = fun k => -deriv d k :=
      funext (quotient_spec _ d unit)
    rw [row]
    have negative := product_scale (-1 : K) (deriv d) d j
    have negMul (x : K) : -1 * x = -x := by grind
    simp only [negMul] at negative
    grind
  funext j
  unfold resolvent at numerator ⊢
  rw [numerator, quotient_product _ _ squareUnit]

/-- A polynomial is a finite list of (degree, coefficient) monomials, in any order. -/
def moment (r : TaylorSeries K) (p : List (Nat × K)) : K :=
  (p.map (fun (j, c) => c * r j)).sum

theorem moment_scale (c : K) (r : TaylorSeries K) (p : List (Nat × K)) :
    moment (fun j => c * r j) p = c * moment r p := by
  induction p with
  | nil => simp [moment, Semiring.mul_zero]
  | cons term rest ih =>
    simp only [moment, List.map_cons, List.sum_cons] at ih ⊢
    grind

end TaylorSeries

namespace XiArithmetic

open Std
variable {K : Type _} [Field K]
attribute [local instance] Semiring.natCast

private def sumBelow (n : Nat) (f : Nat → K) : K :=
  match n with
  | 0 => 0
  | k + 1 => sumBelow k f + f k

private def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

/-- The first m terms of 2 atanh((x-1)/(x+1)), used only at positive arguments. -/
private def logPartial (m : Nat) (x : K) : K :=
  let r := (x - 1) / (x + 1)
  sumBelow m fun k => 2 * r ^ (2 * k + 1) / ((2 * k + 1 : Nat) : K)

/-- Left Riemann sum for the elementary integral of 4/(1+x^2) on [0,1]. -/
private def piPartial (n : Nat) : K :=
  sumBelow n (fun k => 4 / (1 + ((k : K) / (n : K)) ^ 2)) / (n : K)

private def expCoeff (a : K) (j : Nat) : K := a ^ j / ((factorial j : Nat) : K)

private def oneSeries : TaylorSeries K := fun j => if j = 0 then 1 else 0

private def seriesPower (f : TaylorSeries K) : Nat → TaylorSeries K
  | 0 => oneSeries
  | k + 1 => TaylorSeries.product f (seriesPower f k)

private def halfBinomial : Nat → K
  | 0 => 1
  | j + 1 => halfBinomial j * (1 / 2 - (j : K)) / ((j + 1 : Nat) : K)

/-- u(z) = s(z)-2 = (3/2)((1-4z/9)^(1/2)-1), with u(0)=0. -/
private def chartShift : TaylorSeries K
  | 0 => 0
  | j + 1 => (3 / 2 : K) * halfBinomial (j + 1) * (-4 / 9 : K) ^ (j + 1)

private def inChart (f : TaylorSeries K) (j : Nat) : K :=
  sumBelow (j + 1) fun k => f k * seriesPower chartShift k j

/-- Euler's finite gamma product in u=s-2, before its exponential factor. -/
private def gammaProduct : Nat → TaylorSeries K
  | 0 => oneSeries
  | k + 1 =>
    TaylorSeries.product (fun j => (-1 / (2 * ((k + 1 : Nat) : K))) ^ j) (gammaProduct k)

/-- Coefficient j of the finite Euler--Gamma completion in the manuscript's z-coordinate.
The positive cutoff is N=stage+1. Every scalar operation uses rational constants. -/
def completionApprox (weight : Nat → K) (stage : Nat) : TaylorSeries K :=
  let n := stage + 1
  let piN : K := piPartial n
  let logN := logPartial (n * n) (K := K)
  let arch := TaylorSeries.product (expCoeff ((logN (n : K) - logN piN) / 2)) (gammaProduct n)
  let dirichlet := fun j => sumBelow n fun k =>
    let m := k + 1
    weight m / (m : K) ^ 2 * expCoeff (-(logN (m : K))) j
  let pulled := inChart (TaylorSeries.product arch dirichlet)
  fun j => (2 * pulled j - (match j with | 0 => 0 | k + 1 => pulled k)) / piN

/-- The conductor-one character on the positive Dirichlet summation indices. -/
def trivialWeight (n : Nat) : K := if Nat.gcd n 1 = 1 then 1 else 0

def classicalMoment (stage : Nat) : List (Nat × K) → K :=
  TaylorSeries.moment (TaylorSeries.resolvent (completionApprox (fun _ => (1 : K)) stage))

def trivialMoment (stage : Nat) : List (Nat × K) → K :=
  TaylorSeries.moment (TaylorSeries.resolvent (TaylorSeries.product
    (completionApprox trivialWeight stage) (completionApprox (fun n => (trivialWeight n)⁻¹) stage)))

private theorem trivial_weights :
    (trivialWeight (K := K) = fun _ => 1) ∧ ((fun n => (trivialWeight (K := K) n)⁻¹) = fun _ => 1) := by
  constructor <;> funext n <;> simp [trivialWeight, Field.inv_one]

private theorem gamma_zero (n : Nat) : gammaProduct (K := K) n 0 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [gammaProduct, TaylorSeries.product, Semiring.pow_zero, ih, Semiring.one_mul]

private theorem inChart_zero (f : TaylorSeries K) : inChart f 0 = f 0 := by
  change 0 + f 0 * 1 = f 0
  grind

variable [LE K] [LT K] [IsLinearOrder K] [LawfulOrderLT K] [OrderedRing K]

private theorem div_bounds {a d lo hi : K} (pos : 0 < d)
    (lower : lo * d ≤ a) (upper : a ≤ hi * d) : lo ≤ a / d ∧ a / d ≤ hi := by
  rw [Field.div_eq_mul_inv]
  refine ⟨(Field.IsOrdered.le_mul_inv_iff_mul_le _ _ pos).mpr lower, ?_⟩
  have le := OrderedRing.mul_le_mul_of_nonneg_right upper
    (Preorder.le_of_lt (Field.IsOrdered.inv_pos_iff.mpr pos))
  simpa only [Semiring.mul_assoc, Field.mul_inv_cancel (Preorder.ne_of_gt pos), Semiring.mul_one]
    using le

private theorem sum_bounds (n : Nat) (f : Nat → K) (lo hi : K)
    (bounds : ∀ k, k < n → lo ≤ f k ∧ f k ≤ hi) :
    lo * (n : K) ≤ sumBelow n f ∧ sumBelow n f ≤ hi * (n : K) := by
  induction n with
  | zero => simp [sumBelow, Semiring.natCast_zero, Semiring.mul_zero]
  | succ n ih =>
    have first := ih (fun k hk => bounds k (by omega))
    have last := bounds n (by omega)
    simp only [sumBelow, Semiring.natCast_succ]
    grind

private theorem pi_bounds (n : Nat) (hn : 0 < n) : 2 ≤ piPartial (K := K) n ∧ piPartial n ≤ (4 : K) := by
  have pos : (0 : K) < (n : K) := by
    simpa only [Semiring.natCast_zero] using OrderedRing.natCast_lt_natCast_of_lt (R := K) 0 n hn
  have sums := sum_bounds n (fun k => (4 : K) / (1 + ((k : K) / (n : K)) ^ 2)) 2 4 (by
    intro k hk
    have kl : (0 : K) ≤ (k : K) := OrderedRing.natCast_nonneg
    have kr := OrderedRing.natCast_le_natCast_of_le (R := K) k n (by omega)
    have frac := div_bounds pos (lo := 0) (hi := 1) (a := (k : K)) (by grind) (by grind)
    let x := (k : K) / (n : K)
    have hx : 0 ≤ x ∧ x ≤ 1 := frac
    have sq := OrderedRing.mul_nonneg hx.1 hx.1
    have small := OrderedRing.mul_nonneg hx.1 (show 0 ≤ 1 - x by grind)
    change 2 ≤ 4 / (1 + x ^ 2) ∧ 4 / (1 + x ^ 2) ≤ 4
    apply div_bounds <;> grind)
  exact div_bounds pos sums.1 sums.2

private theorem positive_dirichlet_mass (stage : Nat) :
    1 ≤ sumBelow (stage + 1) (fun k => (1 : K) / ((k + 1 : Nat) : K) ^ 2) := by
  induction stage with
  | zero => simp [sumBelow, Semiring.natCast_one]; grind
  | succ n ih =>
    have pos : 0 < (((n + 1 + 1 : Nat) : K)) := by
      simpa only [Semiring.natCast_zero] using
        OrderedRing.natCast_lt_natCast_of_lt (R := K) 0 (n+1+1) (by omega)
    have square := OrderedRing.mul_pos pos pos
    have inv := Field.IsOrdered.inv_pos_iff.mpr square
    rw [sumBelow.eq_2]
    grind

private theorem approx_head (stage : Nat) :
    (1/2 : K) ≤ completionApprox (fun _ => (1 : K)) stage 0 := by
  let n := stage + 1
  have piBounds := pi_bounds (K := K) n (by dsimp [n]; omega)
  have mass := positive_dirichlet_mass (K := K) stage
  have exp_zero (x : K) : expCoeff x 0 = 1 := by
    simp only [expCoeff, factorial, Semiring.natCast_one, Semiring.pow_zero]; grind
  change (1/2 : K) ≤ (2 * inChart _ 0 - 0) / piPartial n
  simp only [inChart_zero, TaylorSeries.product.eq_1, exp_zero, gamma_zero,
    Semiring.mul_one, Semiring.one_mul]
  conv => rhs; rw [Field.div_eq_mul_inv]
  apply (Field.IsOrdered.le_mul_inv_iff_mul_le _ _ (show 0 < piPartial (K := K) n by grind)).mpr
  grind

end XiArithmetic

section XiGerms

open Std
variable {K : Type _} [Field K] [LE K] [LT K] [IsLinearOrder K] [LawfulOrderLT K] [OrderedRing K]

/-- Every arithmetic stage already has the exact moment identity, for every polynomial. -/
theorem grh_trivial_xi_arithmetic (stage : Nat) (q : List (Nat × K)) :
    XiArithmetic.trivialMoment stage q = 2 * XiArithmetic.classicalMoment stage q := by
  unfold XiArithmetic.trivialMoment XiArithmetic.classicalMoment
  rw [(XiArithmetic.trivial_weights (K := K)).2, (XiArithmetic.trivial_weights (K := K)).1]
  have bound := XiArithmetic.approx_head (K := K) stage
  have unit : XiArithmetic.completionApprox (fun _ => (1 : K)) stage 0 ≠ 0 := by grind
  rw [TaylorSeries.resolvent_square _ unit, TaylorSeries.moment_scale]

/-- An order-field sequence converges to x if it is eventually in every open interval about x. -/
def xiCoeffLimit (u : Nat → K) (x : K) : Prop :=
  ∀ a b, a < x → x < b → ∃ N, ∀ n, N ≤ n → a < u n ∧ u n < b

/-- Equality of the actual arithmetic limit predicates, without a convergence witness as a premise. -/
theorem grh_trivial_xi_limit (q : List (Nat × K)) (x : K) :
    xiCoeffLimit (fun n => XiArithmetic.trivialMoment n q) (2 * x) ↔
      xiCoeffLimit (fun n => XiArithmetic.classicalMoment n q) x := by
  constructor
  · intro h a b ha hb
    obtain ⟨N, hn⟩ := h (2*a) (2*b) (by grind) (by grind)
    refine ⟨N, fun n nLarge => ?_⟩
    have bounds := hn n nLarge
    simp only [grh_trivial_xi_arithmetic] at bounds
    grind
  · intro h a b ha hb
    obtain ⟨N, hn⟩ := h (a/2) (b/2) (by grind) (by grind)
    refine ⟨N, fun n nLarge => ?_⟩
    have bounds := hn n nLarge
    simp only [grh_trivial_xi_arithmetic]
    grind

private theorem xi_limit_unique {u : Nat → K} {x y : K}
    (hx : xiCoeffLimit u x) (hy : xiCoeffLimit u y) : x = y := by
  have ordered {a b : K} (ha : xiCoeffLimit u a) (hb : xiCoeffLimit u b) (h : a < b) : False := by
    let mid := (a + b) / 2
    have hm : a < mid ∧ mid < b := by dsimp [mid]; grind
    obtain ⟨n, hn⟩ := ha (a-1) mid (by grind) hm.1
    obtain ⟨m, hk⟩ := hb mid (b+1) hm.2 (by grind)
    have left := (hn (max n m) (Nat.le_max_left ..)).2
    have right := (hk (max n m) (Nat.le_max_right ..)).1
    grind
  grind only [ordered hx hy, ordered hy hx]

/-- A realization of the actual completed function, specified by the coefficient limits of
its arithmetic approximants. Different realizations and dual factors may be supplied. -/
structure XiTaylorGerm (weight : Nat → K) where
  coeff : TaylorSeries K
  limit : ∀ j, xiCoeffLimit (fun n => XiArithmetic.completionApprox weight n j) (coeff j)

private theorem xi_germ_eq {v w : Nat → K} (f : XiTaylorGerm v) (g : XiTaylorGerm w)
    (same : v = w) : f.coeff = g.coeff := by
  subst w
  funext j
  exact xi_limit_unique (f.limit j) (g.limit j)

variable (zeta : XiTaylorGerm (fun _ => (1 : K)))
  (standard : XiTaylorGerm (XiArithmetic.trivialWeight (K := K)))
  (dual : XiTaylorGerm (fun n => (XiArithmetic.trivialWeight (K := K) n)⁻¹))

/-- One certified classical germ supplies both conductor-one inputs. -/
def grh_trivial_xi_factors :
    XiTaylorGerm (XiArithmetic.trivialWeight (K := K)) ×
      XiTaylorGerm (fun n => (XiArithmetic.trivialWeight (K := K) n)⁻¹) :=
  ⟨(XiArithmetic.trivial_weights (K := K)).1.symm ▸ zeta,
   (XiArithmetic.trivial_weights (K := K)).2.symm ▸ zeta⟩

theorem grh_xi_regular : zeta.coeff 0 ≠ 0 := by
  intro zero
  obtain ⟨N, after⟩ := zeta.limit 0 (-1) (1/4) (by grind) (by grind)
  have upper := (after N (Nat.le_refl _)).2
  have lower := XiArithmetic.approx_head (K := K) N
  grind

/-- Conductor one, zero twist: the two independently certified factors both equal xi. -/
theorem grh_trivial_xi_square :
    TaylorSeries.product standard.coeff dual.coeff = TaylorSeries.product zeta.coeff zeta.coeff := by
  have h := xi_germ_eq standard zeta XiArithmetic.trivial_weights.1
  have hd := xi_germ_eq dual zeta XiArithmetic.trivial_weights.2
  rw [h, hd]

theorem grh_trivial_xi_resolvent :
    TaylorSeries.resolvent (TaylorSeries.product standard.coeff dual.coeff) =
      fun j => 2 * TaylorSeries.resolvent zeta.coeff j := by
  rw [grh_trivial_xi_square zeta standard dual]
  exact TaylorSeries.resolvent_square zeta.coeff (grh_xi_regular zeta)

theorem grh_trivial_xi_coeff (j : Nat) :
    TaylorSeries.resolvent (TaylorSeries.product standard.coeff dual.coeff) j =
      2 * TaylorSeries.resolvent zeta.coeff j :=
  congrFun (grh_trivial_xi_resolvent zeta standard dual) j

theorem grh_trivial_xi_moment (q : List (Nat × K)) :
    TaylorSeries.moment (TaylorSeries.resolvent (TaylorSeries.product standard.coeff dual.coeff)) q =
      2 * TaylorSeries.moment (TaylorSeries.resolvent zeta.coeff) q := by
  rw [funext (grh_trivial_xi_coeff zeta standard dual)]
  exact TaylorSeries.moment_scale 2 (TaylorSeries.resolvent zeta.coeff) q

/-- Monomials of t^offset p^2, retaining both cross terms in the finite product. -/
def xiSquareTest (offset : Nat) (p : List (Nat × K)) : List (Nat × K) :=
  p.flatMap fun (i, a) => p.map fun (j, b) => (offset + i + j, a * b)

/-- The fiber identification names its completed product, before taking any moments. -/
theorem grh_trivial_xi_readback {Z : Type _} {Rep : Nat → Type _} (target : ZeroLineSpec Z K)
    (family : (n : Nat) → Rep n → TaylorSeries K) (trivial : Rep 1)
    (atTrivial : family 1 trivial = TaylorSeries.product standard.coeff dual.coeff)
    (familyWitness : ∀ (k : Nat) (π : Rep (k + 1)) (p : List (Nat × K)),
      let r := TaylorSeries.resolvent (family (k + 1) π)
      0 ≤ TaylorSeries.moment r (xiSquareTest 1 p) ∧
        TaylorSeries.moment r (xiSquareTest 1 p) ≤ (4 / 9 : K) * TaylorSeries.moment r (xiSquareTest 0 p))
    (readback : (∀ p : List (Nat × K),
      0 ≤ TaylorSeries.moment (TaylorSeries.resolvent zeta.coeff) (xiSquareTest 1 p) ∧
      TaylorSeries.moment (TaylorSeries.resolvent zeta.coeff) (xiSquareTest 1 p) ≤
        (4 / 9 : K) * TaylorSeries.moment (TaylorSeries.resolvent zeta.coeff) (xiSquareTest 0 p)) →
      target.goal) : target.goal :=
  grh_trivial_moment_readback target trivial (4 / 9)
    (fun n π p => TaylorSeries.moment (TaylorSeries.resolvent (family n π)) (xiSquareTest 1 p))
    (fun n π p => TaylorSeries.moment (TaylorSeries.resolvent (family n π)) (xiSquareTest 0 p))
    (fun p => TaylorSeries.moment (TaylorSeries.resolvent zeta.coeff) (xiSquareTest 1 p))
    (fun p => TaylorSeries.moment (TaylorSeries.resolvent zeta.coeff) (xiSquareTest 0 p))
    (fun p => atTrivial ▸ grh_trivial_xi_moment zeta standard dual (xiSquareTest 1 p))
    (fun p => atTrivial ▸ grh_trivial_xi_moment zeta standard dual (xiSquareTest 0 p))
    familyWitness readback

end XiGerms

end GAlgebra
