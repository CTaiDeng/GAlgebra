import GAlgebra.ArithmeticEnclosures
import GAlgebra.FiniteGeometry

set_option autoImplicit false
namespace GAlgebra

inductive ArithmeticObligation
  | goldbach | twinPrimes | primeTuples | legendre | grandRiemann

def PrimeOffsetsAdmissible (offsets : List Int) : Prop :=
  ∀ q : Nat, TrialPrime q → ∃ r : Int, 0 ≤ r ∧ r < (q : Int) ∧
    ∀ h ∈ offsets, (r + h) % (q : Int) ≠ 0

def ArithmeticObligation.goal (tupleAsymptotic : List Int → Prop)
    (grandRiemann : Prop) : ArithmeticObligation → Prop
  | .goldbach => ∀ n : Nat, 4 ≤ n → n % 2 = 0 →
      ∃ p q : Nat, TrialPrime p ∧ TrialPrime q ∧ p + q = n
  | .twinPrimes => ∀ cutoff : Nat, ∃ p : Nat, cutoff < p ∧ TrialPrime p ∧ TrialPrime (p + 2)
  | .primeTuples => ∀ offsets : List Int, offsets.Nodup → 0 ∈ offsets →
      PrimeOffsetsAdmissible offsets → tupleAsymptotic offsets
  | .legendre => ∀ m : Nat, 1 ≤ m → ∃ p : Nat, TrialPrime p ∧ m ^ 2 < p ∧ p < (m + 1) ^ 2
  | .grandRiemann => grandRiemann

theorem arithmetic_family_readback (tupleAsymptotic : List Int → Prop)
    (grandRiemann : Prop) (valid : ArithmeticObligation → Prop)
    (readback : ∀ σ, valid σ → σ.goal tupleAsymptotic grandRiemann)
    (covered : ∀ σ, valid σ) : ∀ σ : ArithmeticObligation,
      σ.goal tupleAsymptotic grandRiemann :=
  fun σ => readback σ (covered σ)

def primeFiberCoefficient {A B : Type _} [DecidableEq B] (source : List A)
    (relation : A → B) (degree : A → Nat) (weight : A → Rat) (target : B) (total : Nat) : Rat :=
  finiteSum (fun a => if relation a = target ∧ degree a = total then weight a else 0) source

theorem prime_fiber_cutoff {A B : Type _} [DecidableEq B] (source : List A)
    (relation : A → B) (degree : A → Nat) (weight : A → Rat) (target : B) (total : Nat)
    (keep : A → Bool) (covers : ∀ a ∈ source, degree a = total → keep a = true) :
    primeFiberCoefficient (source.filter keep) relation degree weight target total =
      primeFiberCoefficient source relation degree weight target total := by
  induction source with
  | nil => rfl
  | cons a rest ih =>
    have tail := ih (fun i hi => covers i (List.mem_cons_of_mem a hi))
    unfold primeFiberCoefficient at tail ⊢
    by_cases kept : keep a = true
    · simp only [List.filter_cons_of_pos kept, finiteSum, tail]
    · have offDegree : degree a ≠ total := fun equal => kept (covers a List.mem_cons_self equal)
      simp only [List.filter_cons_of_neg kept, finiteSum, offDegree, and_false, ite_false,
        Rat.zero_add, tail]

theorem prime_fiber_coarsening {A B C : Type _} [DecidableEq B] [DecidableEq C]
    (source : List A) (keys : List B) (unique : keys.Nodup)
    (relation : A → B) (degree : A → Nat) (weight : A → Rat) (coarsen : B → C)
    (target : C) (total : Nat) (covers : ∀ a ∈ source, relation a ∈ keys) :
    primeFiberCoefficient source (fun a => coarsen (relation a)) degree weight target total =
      finiteSum (fun key => if coarsen key = target then
        primeFiberCoefficient source relation degree weight key total else 0) keys := by
  let fiber (a : A) (key : B) : Rat :=
    if relation a = key ∧ degree a = total ∧ coarsen key = target then weight a else 0
  calc
    _ = finiteSum (fun a => finiteSum (fiber a) keys) source := by
      unfold primeFiberCoefficient
      apply finiteSum_congr_members
      intro a ha
      have isolated := finiteSum_single_of_nodup (fiber a) unique (covers a ha)
        (fun key _ other => by simp [fiber, Ne.symm other])
      rw [isolated]
      simp [fiber, And.comm]
    _ = finiteSum (fun key => finiteSum (fun a => fiber a key) source) keys :=
      finite_sum_swap source keys fiber
    _ = _ := by
      apply finiteSum_congr
      intro key
      by_cases sameTarget : coarsen key = target
      · rw [ite_eq_left sameTarget]
        unfold primeFiberCoefficient
        apply finiteSum_congr
        intro a
        simp [fiber, sameTarget]
      · rw [ite_eq_right sameTarget]
        exact finiteSum_zero_of_members source (fun a _ => by simp [fiber, sameTarget])

theorem prime_finite_mass_positive_iff {A : Type _} (source : List A) (weight : A → Rat)
    (nonnegative : ∀ a, 0 ≤ weight a) :
    0 < finiteSum weight source ↔ ∃ a ∈ source, 0 < weight a := by
  classical
  have certificate := nonnegative_sum_zero weight (Rat.le_refl (a := 0))
    (fun x y hx hy => Rat.add_nonneg hx hy)
    (fun x y hx hy zero => by grind) nonnegative source
  constructor
  · intro positive
    by_cases witness : ∃ a ∈ source, 0 < weight a
    · exact witness
    · have zero := certificate.2.mpr (fun a ha => by
        have notPositive : ¬ 0 < weight a := fun h => witness ⟨a, ha, h⟩
        exact Rat.le_antisymm (Rat.not_lt.mp notPositive) (nonnegative a))
      exact False.elim ((Rat.ne_of_gt positive) zero)
  · rintro ⟨a, ha, positive⟩
    by_cases zero : finiteSum weight source = 0
    · exact False.elim ((Rat.ne_of_gt positive) (certificate.2.mp zero a ha))
    · exact Rat.lt_of_le_of_ne certificate.1 (Ne.symm zero)

theorem prime_phase_margin_readback (main error size c δ : Rat)
    (mainLower : c * size ≤ main) (errorLower : -(c - δ) * size ≤ error) :
    δ * size ≤ main + error := by
  grind

theorem prime_dyadic_growth (counts : Nat → Rat) (δ : Rat)
    (increments : ∀ j, δ ≤ counts (j + 1) - counts j) (J : Nat) :
    counts 0 + (J : Rat) * δ ≤ counts J := by
  induction J with
  | zero => simp
  | succ j ih =>
    have step := increments j
    change counts 0 + ((j + 1 : Nat) : Rat) * δ ≤ counts (j + 1)
    rw [Rat.natCast_add, Rat.add_mul]
    simpa using (show counts 0 + ((j : Rat) * δ + 1 * δ) ≤ counts (j + 1) by grind)

theorem twin_offsets_admissible : PrimeOffsetsAdmissible [0, 2] := by
  intro q prime
  have lower : (2 : Int) ≤ (q : Int) := by have := prime.1; omega
  let r : Int := (q : Int) - 1
  refine ⟨r, by dsimp [r]; omega, by dsimp [r]; omega, ?_⟩
  intro h member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with equal | equal
  · subst h
    have ordinary : r % (q : Int) = r := Int.emod_eq_of_lt (by dsimp [r]; omega) (by dsimp [r]; omega)
    rw [Int.add_zero, ordinary]
    dsimp [r]
    omega
  · subst h
    have shift : r + 2 = (1 : Int) + (q : Int) := by dsimp [r]; omega
    rw [shift, Int.add_emod_right, Int.emod_eq_of_lt (by decide) (by omega)]
    decide

theorem prime_tuple_implies_twins (tupleAsymptotic : List Int → Prop) (grandRiemann : Prop)
    (full : ArithmeticObligation.primeTuples.goal tupleAsymptotic grandRiemann)
    (weight : Nat → Rat)
    (support : ∀ n, weight n ≠ 0 → TrialPrime n ∧ TrialPrime (n + 2))
    (growth : tupleAsymptotic [0, 2] → ∀ cutoff : Nat, ∃ size : Nat, cutoff < size ∧
      finiteSum weight (List.range (cutoff + 1)) < finiteSum weight (List.range size)) :
    ArithmeticObligation.twinPrimes.goal tupleAsymptotic grandRiemann := by
  have asymptotic := full [0, 2] (by decide) (by decide) twin_offsets_admissible
  intro cutoff
  obtain ⟨size, large, more⟩ := growth asymptotic cutoff
  have split : size = cutoff + 1 + (size - (cutoff + 1)) := by omega
  let tail := (List.range (size - (cutoff + 1))).map (fun n => cutoff + 1 + n)
  have cover : List.range size = List.range (cutoff + 1) ++ tail := by
    simpa only [tail, ← List.range_add] using congrArg List.range split
  rw [cover, finiteSum_append] at more
  by_cases found : ∃ n ∈ tail, weight n ≠ 0
  · obtain ⟨n, hn, nonzero⟩ := found
    obtain ⟨i, _, address⟩ := List.mem_map.mp hn
    obtain ⟨p, q⟩ := support n nonzero
    exact ⟨n, by omega, p, q⟩
  · have zero := finiteSum_zero_of_members tail (fun n hn => by
      by_cases hz : weight n = 0
      · exact hz
      · exact False.elim (found ⟨n, hn, hz⟩))
    simp [zero] at more

end GAlgebra
