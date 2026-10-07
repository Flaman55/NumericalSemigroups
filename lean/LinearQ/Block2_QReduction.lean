import Mathlib
import LinearQ.Block1_KIntervals

/-!
# Block 2: Quadratic form Q and its linear-time reduction (two generators)

Uses kernelK_spec from Block 1 to simplify all case work.
Windows defined with if-then-else instead of Finset.filter
for better simp_rw compatibility.
-/

namespace LinearQ

/-- The quadratic form Q -/
noncomputable def quadForm (a b : ℕ) (G : Finset ℤ) (n : ℤ → ℝ) : ℝ :=
  ∑ i ∈ G, ∑ j ∈ G, (kernelK a b (j - i) : ℝ) * n i * n j

/-- Positive window: sum of n(j) for j in [k, k+a) ∩ G -/
noncomputable def windowPos (a : ℕ) (G : Finset ℤ) (n : ℤ → ℝ) (k : ℤ) : ℝ :=
  ∑ j ∈ G, if k ≤ j ∧ j < k + (a : ℤ) then n j else 0

/-- Negative window: sum of n(j) for j in [k+b, k+a+b) ∩ G -/
noncomputable def windowNeg (a b : ℕ) (G : Finset ℤ) (n : ℤ → ℝ) (k : ℤ) : ℝ :=
  ∑ j ∈ G, if k + (b : ℤ) ≤ j ∧ j < k + (a : ℤ) + b then n j else 0

/-- The linear form: Σ_k n(k) * (W⁺(k) - W⁻(k)) -/
noncomputable def linearForm (a b : ℕ) (G : Finset ℤ) (n : ℤ → ℝ) : ℝ :=
  ∑ k ∈ G, n k * (windowPos a G n k - windowNeg a b G n k)

/-! ## Key lemmas using kernelK_spec -/

/-- K(j-i) = 1 iff i ≤ j < i+a -/
lemma kernelK_eq_one_iff (a b : ℕ) (hab : a < b) (i j : ℤ) :
    kernelK a b (j - i) = 1 ↔ i ≤ j ∧ j < i + (a : ℤ) := by
  have hlt : (a : ℤ) < b := Int.ofNat_lt.mpr hab
  rw [kernelK_spec a b hab]
  constructor
  · intro h; split_ifs at h <;> omega
  · intro ⟨hi, hj⟩; split_ifs <;> omega

/-- K(j-i) = -1 iff i+b ≤ j < i+a+b -/
lemma kernelK_eq_neg_one_iff (a b : ℕ) (hab : a < b) (i j : ℤ) :
    kernelK a b (j - i) = -1 ↔ i + (b : ℤ) ≤ j ∧ j < i + (a : ℤ) + b := by
  have hlt : (a : ℤ) < b := Int.ofNat_lt.mpr hab
  rw [kernelK_spec a b hab]
  constructor
  · intro h; split_ifs at h; omega
  · intro ⟨hi, hj⟩; split_ifs <;> omega

/-- Pointwise: K(j-i)*n(j) = pos_part - neg_part -/
lemma kernelK_mul_eq (a b : ℕ) (hab : a < b) (i j : ℤ) (nj : ℝ) :
    (kernelK a b (j - i) : ℝ) * nj =
    (if i ≤ j ∧ j < i + (a : ℤ) then nj else 0) -
    (if i + (b : ℤ) ≤ j ∧ j < i + (a : ℤ) + b then nj else 0) := by
  have hlt : (a : ℤ) < b := Int.ofNat_lt.mpr hab
  by_cases h1 : i ≤ j ∧ j < i + (a : ℤ)
  · have hk : kernelK a b (j - i) = 1 := (kernelK_eq_one_iff a b hab i j).mpr h1
    have h2 : ¬(i + (b : ℤ) ≤ j ∧ j < i + (a : ℤ) + b) := by
      push Not; obtain ⟨_, hj⟩ := h1; intro; linarith
    simp [h1, h2, hk]
  · by_cases h2 : i + (b : ℤ) ≤ j ∧ j < i + (a : ℤ) + b
    · have hk : kernelK a b (j - i) = -1 := (kernelK_eq_neg_one_iff a b hab i j).mpr h2
      simp [h1, h2, hk]
    · have hk : kernelK a b (j - i) = 0 := by
        rw [kernelK_spec a b hab]
        split_ifs <;> push Not at h1 h2 <;> omega
      simp [h1, h2, hk]

/-- For fixed i: Σ_j K(j-i)*n(j) = W⁺(i) - W⁻(i) -/
lemma inner_sum_eq_window_diff (a b : ℕ) (hab : a < b)
    (G : Finset ℤ) (n : ℤ → ℝ) (i : ℤ) :
    ∑ j ∈ G, (kernelK a b (j - i) : ℝ) * n j =
    windowPos a G n i - windowNeg a b G n i := by
  simp only [windowPos, windowNeg]
  rw [← Finset.sum_sub_distrib]
  congr 1; ext j
  exact kernelK_mul_eq a b hab i j (n j)

/-- Main theorem: Q(n) = linearForm(n) -/
theorem quadForm_eq_linearForm (a b : ℕ) (hab : a < b)
    (G : Finset ℤ) (n : ℤ → ℝ) :
    quadForm a b G n = linearForm a b G n := by
  simp only [quadForm, linearForm]
  congr 1; ext i
  have : ∑ j ∈ G, (kernelK a b (j - i) : ℝ) * n i * n j =
         n i * ∑ j ∈ G, (kernelK a b (j - i) : ℝ) * n j := by
    rw [Finset.mul_sum]; congr 1; ext j; ring
  rw [this, inner_sum_eq_window_diff a b hab G n i]

end LinearQ
