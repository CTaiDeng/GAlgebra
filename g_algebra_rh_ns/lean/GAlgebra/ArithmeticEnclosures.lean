import GAlgebra.IntervalSequence

set_option autoImplicit false
namespace GAlgebra

def naturalStrictCeiling (q : Rat) : Nat := q.ceil.toNat + 1

theorem natural_strict_ceiling_bound (q : Rat) (nonnegative : 0 ≤ q) :
    q < (naturalStrictCeiling q : Rat) := by
  have ceiling_bound : q ≤ (q.ceil : Rat) := Rat.le_ceil
  have k_nonnegative : 0 ≤ q.ceil :=
    Rat.intCast_nonneg.mp (Rat.le_trans nonnegative ceiling_bound)
  have cast_ceiling : ((q.ceil.toNat : Nat) : Rat) = (q.ceil : Rat) := by
    rw [← Rat.intCast_natCast, Int.toNat_of_nonneg k_nonnegative]
  unfold naturalStrictCeiling
  rw [Rat.natCast_add, cast_ceiling]
  change q < (q.ceil : Rat) + 1
  grind

theorem rat_reciprocal_eventually_lt (ε : Rat) (positive : 0 < ε) :
    ∃ n : Nat, 0 < n ∧ 1 / (n : Rat) < ε := by
  let n := naturalStrictCeiling (1 / ε)
  have reciprocal_positive : 0 < 1 / ε := (Rat.lt_div_iff positive).mpr (by grind)
  have n_positive : 0 < n := by
    dsimp [n, naturalStrictCeiling]
    omega
  have smaller : 1 / ε < (n : Rat) :=
    natural_strict_ceiling_bound (1 / ε) (Rat.le_of_lt reciprocal_positive)
  have product := (Rat.div_lt_iff positive).mp smaller
  refine ⟨n, n_positive, (Rat.div_lt_iff (Rat.natCast_pos.mpr n_positive)).mpr ?_⟩
  simpa [Rat.mul_comm] using product

private theorem interval_of_steps_mono (f : Nat → Rat) (step : ∀ n, f n ≤ f (n + 1)) :
    ∀ n m, n ≤ m → f n ≤ f m := by
  intro n m
  induction m with
  | zero =>
    intro h
    have eq : n = 0 := by omega
    rw [eq]
    grind
  | succ m ih =>
    intro h
    by_cases same : n = m + 1
    · rw [same]
      grind
    · exact Rat.le_trans (ih (by omega)) (step m)

def IntervalSequence.ofSteps (bounds : Nat → RationalInterval)
    (valid : ∀ n, (bounds n).lower ≤ (bounds n).upper)
    (lower_step : ∀ n, (bounds n).lower ≤ (bounds (n + 1)).lower)
    (upper_step : ∀ n, (bounds (n + 1)).upper ≤ (bounds n).upper)
    (precise : ∀ ε : Rat, 0 < ε → ∃ n, (bounds n).upper - (bounds n).lower < ε) :
    IntervalSequence where
  bounds := bounds
  valid := valid
  lower_mono := interval_of_steps_mono (fun n => (bounds n).lower) lower_step
  upper_anti n m h := by
    have neg_upper := interval_of_steps_mono (fun n => -(bounds n).upper)
      (fun i => by have hi := upper_step i; grind) n m h
    grind
  precise := precise

theorem bounded_geometric_power_goes_small (q : Rat) (nonnegative : 0 ≤ q)
    (at_most_half : q ≤ 1 / 2) (ε : Rat) (positive : 0 < ε) :
    ∃ n : Nat, q ^ n < ε := by
  have scaled_power (n : Nat) : ((n : Rat) + 1) * q ^ n ≤ 1 := by
    induction n with
    | zero => simp
    | succ n ih =>
      have factor_nonnegative : 0 ≤ (n : Rat) + 2 := by
        have := Rat.natCast_nonneg (a := n)
        grind
      have half := Rat.mul_le_mul_of_nonneg_left at_most_half factor_nonnegative
      have factor : ((n : Rat) + 2) * q ≤ (n : Rat) + 1 := by
        have := Rat.natCast_nonneg (a := n)
        grind
      have bound := Rat.mul_le_mul_of_nonneg_right factor
        (Rat.pow_nonneg (n := n) nonnegative)
      change (((n + 1 : Nat) : Rat) + 1) * q ^ (n + 1) ≤ 1
      rw [Rat.natCast_add, Rat.pow_succ]
      change (((n : Rat) + 1) + 1) * (q ^ n * q) ≤ 1
      grind
  obtain ⟨n, hn, small⟩ := rat_reciprocal_eventually_lt ε positive
  have n_positive := Rat.natCast_pos.mpr hn
  have product := (Rat.div_lt_iff n_positive).mp small
  have scaled := scaled_power n
  have power_nonnegative := Rat.pow_nonneg (n := n) nonnegative
  have less : q ^ n * (n : Rat) < ε * (n : Rat) := by grind
  exact ⟨n, (Rat.mul_lt_mul_right n_positive).mp less⟩

def rationalPartialSum (term : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => rationalPartialSum term n + term n

def atanhLogTerm (r : Rat) (n : Nat) : Rat :=
  (2 * r * (r * r) ^ n) / (2 * (n : Rat) + 1)

def atanhLogPartial (r : Rat) (n : Nat) : Rat :=
  rationalPartialSum (atanhLogTerm r) n

def atanhLogBounds (r : Rat) (n : Nat) : RationalInterval :=
  ⟨atanhLogPartial r n, atanhLogPartial r n + 3 * r * (r * r) ^ n⟩

theorem atanh_log_term_bounds (r : Rat) (nonnegative : 0 ≤ r) (n : Nat) :
    0 ≤ atanhLogTerm r n ∧ atanhLogTerm r n ≤ 2 * r * (r * r) ^ n := by
  let denominator := 2 * (n : Rat) + 1
  let numerator := 2 * r * (r * r) ^ n
  have denominator_large : 1 ≤ denominator := by
    have := Rat.natCast_nonneg (a := n)
    dsimp [denominator]
    grind
  have denominator_positive : 0 < denominator := by grind
  have square_nonnegative := Rat.mul_nonneg nonnegative nonnegative
  have power_nonnegative := Rat.pow_nonneg (n := n) square_nonnegative
  have numerator_nonnegative : 0 ≤ numerator := by
    dsimp [numerator]
    exact Rat.mul_nonneg (by grind) power_nonnegative
  have cancel : (numerator / denominator) * denominator = numerator :=
    Rat.div_mul_cancel (Rat.ne_of_gt denominator_positive)
  change 0 ≤ numerator / denominator ∧ numerator / denominator ≤ numerator
  constructor
  · by_cases nonnegative_quotient : 0 ≤ numerator / denominator
    · exact nonnegative_quotient
    · have negative : numerator / denominator < 0 := by grind
      have scaled := (Rat.mul_lt_mul_right denominator_positive).mpr negative
      grind
  · have product := Rat.mul_le_mul_of_nonneg_left denominator_large numerator_nonnegative
    by_cases upper : numerator / denominator ≤ numerator
    · exact upper
    · have larger : numerator < numerator / denominator := by grind
      have scaled := (Rat.mul_lt_mul_right denominator_positive).mpr larger
      grind

private theorem small_square (r : Rat) (nonnegative : 0 ≤ r) (third : r ≤ 1 / 3) :
    r * r ≤ 1 / 9 := by
  have first := Rat.mul_le_mul_of_nonneg_right third nonnegative
  have second := Rat.mul_le_mul_of_nonneg_left third (by grind : 0 ≤ (1 / 3 : Rat))
  grind

def atanhLogSequence (r : Rat) (nonnegative : 0 ≤ r) (third : r ≤ 1 / 3) :
    IntervalSequence :=
  IntervalSequence.ofSteps (atanhLogBounds r)
    (fun n => by
      have power_nonnegative := Rat.pow_nonneg (n := n) (Rat.mul_nonneg nonnegative nonnegative)
      have tail_nonnegative := Rat.mul_nonneg (show 0 ≤ 3 * r by grind) power_nonnegative
      change atanhLogPartial r n ≤ atanhLogPartial r n + 3 * r * (r * r) ^ n
      grind)
    (fun n => by
      have term_nonnegative := (atanh_log_term_bounds r nonnegative n).1
      change atanhLogPartial r n ≤ atanhLogPartial r n + atanhLogTerm r n
      grind)
    (fun n => by
      have term_upper := (atanh_log_term_bounds r nonnegative n).2
      have square := small_square r nonnegative third
      have power_nonnegative := Rat.pow_nonneg (n := n) (Rat.mul_nonneg nonnegative nonnegative)
      have coefficient : 3 * (r * r) ≤ 1 := by grind
      have tail := Rat.mul_le_mul_of_nonneg_right coefficient
        (Rat.mul_nonneg nonnegative power_nonnegative)
      change
        atanhLogPartial r n + atanhLogTerm r n + 3 * r * (r * r) ^ (n + 1) ≤
        atanhLogPartial r n + 3 * r * (r * r) ^ n
      rw [Rat.pow_succ]
      grind)
    (fun ε positive => by
      have square_nonnegative := Rat.mul_nonneg nonnegative nonnegative
      have square := small_square r nonnegative third
      obtain ⟨n, narrow⟩ := bounded_geometric_power_goes_small (r * r)
        square_nonnegative (by grind) ε positive
      have tail := Rat.mul_le_mul_of_nonneg_right (show 3 * r ≤ 1 by grind)
        (Rat.pow_nonneg (n := n) square_nonnegative)
      refine ⟨n, ?_⟩
      change atanhLogPartial r n + 3 * r * (r * r) ^ n - atanhLogPartial r n < ε
      grind)

private theorem atanh_ratio_bounds (x : Rat) (lower : 1 ≤ x) (upper : x ≤ 2) :
    0 ≤ (x - 1) / (x + 1) ∧ (x - 1) / (x + 1) ≤ 1 / 3 := by
  have positive : 0 < x + 1 := by grind
  constructor
  · by_cases nonnegative : 0 ≤ (x - 1) / (x + 1)
    · exact nonnegative
    · have negative : (x - 1) / (x + 1) < 0 := by grind
      have absurd := (Rat.div_lt_iff positive).mp negative
      grind
  · by_cases bound : (x - 1) / (x + 1) ≤ 1 / 3
    · exact bound
    · have larger : (1 / 3 : Rat) < (x - 1) / (x + 1) := by grind
      have absurd := (Rat.lt_div_iff positive).mp larger
      grind

def unitLogSequence (x : Rat) (lower : 1 ≤ x) (upper : x ≤ 2) : IntervalSequence :=
  atanhLogSequence ((x - 1) / (x + 1))
    (atanh_ratio_bounds x lower upper).1 (atanh_ratio_bounds x lower upper).2

def dyadicMantissa (n : Nat) : Rat := (n : Rat) / ((2 ^ n.log2 : Nat) : Rat)

theorem dyadic_mantissa_bounds (n : Nat) (positive : 0 < n) :
    1 ≤ dyadicMantissa n ∧ dyadicMantissa n ≤ 2 := by
  have hlog := (Nat.log2_eq_iff (Nat.ne_of_gt positive)).mp (rfl : n.log2 = n.log2)
  have denominator_positive : 0 < ((2 ^ n.log2 : Nat) : Rat) :=
    Rat.natCast_pos.mpr (Nat.pow_pos (by decide))
  have lower := Rat.natCast_le_natCast.mpr hlog.1
  have upper := Rat.natCast_lt_natCast.mpr hlog.2
  rw [Nat.pow_succ, Rat.natCast_mul] at upper
  constructor
  · by_cases bound : 1 ≤ dyadicMantissa n
    · exact bound
    · have failure : dyadicMantissa n < 1 := by grind
      have absurd := (Rat.div_lt_iff denominator_positive).mp failure
      grind
  · apply Rat.le_of_lt
    apply (Rat.div_lt_iff denominator_positive).mpr
    simpa [Rat.mul_comm] using upper

def IntervalSequence.repeatAdd (box : IntervalSequence) : Nat → IntervalSequence
  | 0 => point 0
  | n + 1 => (repeatAdd box n).add box

def naturalLogSequence (n : Nat) (positive : 0 < n) : IntervalSequence :=
  let logTwo := unitLogSequence 2 (by decide) (by decide)
  (logTwo.repeatAdd n.log2).add
    (unitLogSequence (dyadicMantissa n) (dyadic_mantissa_bounds n positive).1
      (dyadic_mantissa_bounds n positive).2)

def TrialPrime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, 2 ≤ d → d < p → p % d ≠ 0

def trialPrime (p : Nat) : Bool :=
  decide (2 ≤ p) && (List.range' 2 (p - 2)).all (fun d => decide (p % d ≠ 0))

theorem trial_prime_correct (p : Nat) : trialPrime p = true ↔ TrialPrime p := by
  simp only [trialPrime, TrialPrime, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range'_1]
  constructor
  · rintro ⟨size, no_factor⟩
    exact ⟨size, fun d lower upper => no_factor d ⟨lower, by omega⟩⟩
  · rintro ⟨size, no_factor⟩
    exact ⟨size, fun d hd => no_factor d hd.1 (by have := hd.2; omega)⟩

def primePowerBase (n : Nat) : Option Nat :=
  (List.range' 2 (n - 1)).find? (fun p =>
    (List.range' 1 n.log2).any (fun k => decide (p ^ k = n)) && trialPrime p)

theorem prime_power_base_sound {n p : Nat} (found : primePowerBase n = some p) :
    TrialPrime p ∧ ∃ k : Nat, 1 ≤ k ∧ p ^ k = n := by
  have h := List.find?_some found
  simp only [Bool.and_eq_true, List.any_eq_true, List.mem_range'_1, decide_eq_true_eq] at h
  obtain ⟨⟨k, range, equation⟩, prime⟩ := h
  exact ⟨(trial_prime_correct p).mp prime, k, range.1, equation⟩

theorem prime_power_base_exists {n p k : Nat}
    (prime : TrialPrime p) (exponent_positive : 1 ≤ k) (power : p ^ k = n) :
    (primePowerBase n).isSome := by
  have p_positive : 0 < p := by have := prime.1; omega
  have p_le_n : p ≤ n := by
    simpa [power] using Nat.pow_le_pow_right p_positive exponent_positive
  have n_positive : 0 < n := by omega
  have two_power_le : 2 ^ k ≤ n := power ▸ Nat.pow_le_pow_left prime.1 k
  have k_le_log := (Nat.le_log2 (Nat.ne_of_gt n_positive)).mpr two_power_le
  apply List.find?_isSome.mpr
  refine ⟨p, List.mem_range'_1.mpr ⟨prime.1, by omega⟩, ?_⟩
  simp only [Bool.and_eq_true]
  exact ⟨List.any_eq_true.mpr ⟨k, List.mem_range'_1.mpr ⟨exponent_positive, by omega⟩,
      decide_eq_true_eq.mpr power⟩, (trial_prime_correct p).mpr prime⟩

private theorem trial_prime_divisor {d p : Nat} (prime : TrialPrime p) (dvd : d ∣ p) :
    d = 1 ∨ d = p := by
  by_cases one : d = 1
  · exact Or.inl one
  · right
    have p_positive : 0 < p := by have := prime.1; omega
    have d_positive : 0 < d := by
      by_cases zero : d = 0
      · rw [zero] at dvd
        have p_zero := Nat.eq_zero_of_zero_dvd dvd
        omega
      · omega
    have below := Nat.le_of_dvd p_positive dvd
    by_cases equal : d = p
    · exact equal
    · exact False.elim ((prime.2 d (by omega) (by omega)) (Nat.mod_eq_zero_of_dvd dvd))

theorem prime_power_base_unique {p q k l : Nat}
    (p_prime : TrialPrime p) (q_prime : TrialPrime q) (k_positive : 1 ≤ k)
    (power : p ^ k = q ^ l) : p = q := by
  by_cases equal : p = q
  · exact equal
  · have coprime : Nat.Coprime p q := by
      obtain one | p_eq := trial_prime_divisor p_prime (Nat.gcd_dvd_left p q)
      · exact one
      · obtain one | q_eq := trial_prime_divisor q_prime (Nat.gcd_dvd_right p q)
        · exact one
        · exact False.elim (equal (p_eq.symm.trans q_eq))
    have coprime_power : Nat.Coprime p (q ^ l) := by
      clear power
      induction l with
      | zero => simp [Nat.Coprime]
      | succ l ih =>
        rw [Nat.pow_succ]
        exact ih.mul_right coprime
    have divides_power : p ∣ p ^ k := by
      cases k with
      | zero => omega
      | succ k =>
        rw [Nat.pow_succ]
        exact Nat.dvd_mul_left p (p ^ k)
    rw [power] at divides_power
    exact False.elim (Nat.not_coprime_of_dvd_of_dvd (by have := p_prime.1; omega)
      (Nat.dvd_refl p) divides_power coprime_power)

def mangoldtLogSequence (n : Nat) : IntervalSequence :=
  match found : primePowerBase n with
  | none => IntervalSequence.point 0
  | some p => naturalLogSequence p (by have := (prime_power_base_sound found).1.1; omega)

theorem prime_power_base_exact {n p k : Nat}
    (prime : TrialPrime p) (exponent_positive : 1 ≤ k) (power : p ^ k = n) :
    primePowerBase n = some p := by
  have present := prime_power_base_exists prime exponent_positive power
  cases found : primePowerBase n with
  | none => simp [found] at present
  | some q =>
    obtain ⟨q_prime, j, _, q_power⟩ := prime_power_base_sound found
    have equal := prime_power_base_unique prime q_prime exponent_positive (power.trans q_power.symm)
    rw [equal]

end GAlgebra
