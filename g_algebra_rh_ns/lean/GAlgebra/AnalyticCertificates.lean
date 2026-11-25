import GAlgebra.FiniteGeometry
import GAlgebra.Targets

set_option autoImplicit false
namespace GAlgebra

theorem cone_dual_certificate_sound {I V : Type _} [Abelian V]
    (is : List I) (v : I → V) (scale : Rat → V → V) (L : AddMap V Rat)
    (linear : ∀ c x, L (scale c x) = c * L x)
    (dual : ∀ i, 0 ≤ L (v i)) {target : V} (negative : L target < 0) :
    ¬ ∃ c : I → Rat, (∀ i, 0 ≤ c i) ∧
      finiteSum (fun i => scale (c i) (v i)) is = target := by
  rintro ⟨c, hc, hp⟩
  have calculated : L target = finiteSum (fun i => c i * L (v i)) is := by
    rw [← hp, finiteSum_map]
    exact finiteSum_congr (fun i => linear (c i) (v i)) is
  have h := nonnegative_sum_zero (fun i => c i * L (v i))
    (by decide) (fun _ _ _ _ => by grind) (fun _ _ _ _ _ => by grind)
    (fun i => Rat.mul_nonneg (hc i) (dual i)) is
  rw [← calculated] at h
  grind [h.1]

theorem reflected_zero_from_completed_equation {Z K : Type _} [Mul K] [Zero K]
    (zeta completion completed : Z → K) (mirror : Z → Z)
    (product : ∀ z, completed z = completion z * zeta z)
    (symmetry : ∀ z, completed (mirror z) = completed z)
    (mul_zero : ∀ x : K, x * 0 = 0)
    (left_regular : ∀ z t, zeta z = 0 → completion (mirror z) * t = 0 → t = 0)
    {z : Z} (zero : zeta z = 0) : zeta (mirror z) = 0 := by
  apply left_regular z _ zero
  rw [← product, symmetry, product, zero, mul_zero]

theorem cosine_quadratic_weight (c : Rat) :
    3 + 4 * c + (2 * c ^ 2 - 1) = 2 * (1 + c) ^ 2 := by
  grind

end GAlgebra
