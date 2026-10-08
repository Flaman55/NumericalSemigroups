module

public import Mathlib
public import LinearQ.Block3_MultiGenerator
public import LinearQ.Block3_Windows

/-!
# Block 5: Breakpoint decomposition of the multi-generator quadratic form

For generators `ps ≠ []`, the kernel `K^(ps)` is a step function: it is the telescoping sum of its
jumps `π(s) = K(s) − K(s−1)`, which are nonzero only at the breakpoints, all of which lie in
`[0, σ(ps)]`. Hence the quadratic form
`Q(n) = ∑_{i,j ∈ G} K^(ps)(j − i) · n_i · n_j`
decomposes as a sum over breakpoints of the jump times a tail pair-sum:

  Q(n) = ∑_{s ∈ breakpoints} π(s) · T(s),   T(s) = ∑_{i,j ∈ G, j − i ≥ s} n_i · n_j.

This is the mathematical content behind the sliding-window algorithm for `n` generators: the
number of terms is the number of breakpoints, which is at most `σ(ps) + 1`.

* `kernelK_multi_eq_sum_jump`: `K^(ps)` as a sum of jumps.
* `kernelJump_cons`: parity recurrence `π_{p::ps}(s) = π_ps(s) − π_ps(s − p)`.
* `kernelJump_cons_ne_zero`: a breakpoint of `p :: ps` is a breakpoint of `ps` or a shift of one.
* `quadFormMulti_eq_breakpoint_sum`: the decomposition of `Q`.
-/

namespace LinearQ

/-- Parity recurrence: `π_{p::ps}(s) = π_ps(s) − π_ps(s − p)`. -/
public theorem kernelJump_cons (p : ℕ) (ps : List ℕ) (s : ℤ) :
    kernelJump (p :: ps) s = kernelJump ps s - kernelJump ps (s - p) := by
  have e : s - 1 - (p : ℤ) = s - (p : ℤ) - 1 := by ring
  simp only [kernelJump, kernelK_multi_cons, e]
  ring

/-- A breakpoint of `p :: ps` is a breakpoint of `ps`, or a breakpoint of `ps` shifted by `p`. -/
public theorem kernelJump_cons_ne_zero (p : ℕ) (ps : List ℕ) (s : ℤ)
    (h : kernelJump (p :: ps) s ≠ 0) :
    kernelJump ps s ≠ 0 ∨ kernelJump ps (s - p) ≠ 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := hc
  apply h
  rw [kernelJump_cons, h1, h2]
  ring

/-- Telescoping of the jumps up to a natural bound `m`. -/
public theorem kernelK_multi_telescope (ps : List ℕ) (d : ℤ) (hd : 0 ≤ d) (m : ℕ) :
    (∑ k ∈ Finset.range m, if (k : ℤ) ≤ d then kernelJump ps (k : ℤ) else 0)
      = kernelK_multi ps (min ((m : ℤ) - 1) d) := by
  induction m with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, Nat.cast_zero]
    rw [min_eq_left (show (0 : ℤ) - 1 ≤ d by omega)]
    exact (kernelK_multi_neg ps _ (by omega)).symm
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hcast : ((m + 1 : ℕ) : ℤ) - 1 = (m : ℤ) := by push_cast; ring
    by_cases h : (m : ℤ) ≤ d
    · have e1 : min ((m : ℤ) - 1) d = (m : ℤ) - 1 := min_eq_left (by omega)
      have e2 : min (((m + 1 : ℕ) : ℤ) - 1) d = (m : ℤ) := by
        rw [hcast]
        exact min_eq_left h
      rw [e1, e2]
      simp only [h, ↓reduceIte, kernelJump]
      ring
    · have e1 : min ((m : ℤ) - 1) d = d := min_eq_right (by omega)
      have e2 : min (((m + 1 : ℕ) : ℤ) - 1) d = d := by
        rw [hcast]
        exact min_eq_right (by omega)
      rw [e1, e2]
      simp only [h, ↓reduceIte, add_zero]

/-- `K^(ps)` is the sum of its jumps at the breakpoints `s ≤ d`. -/
public theorem kernelK_multi_eq_sum_jump (ps : List ℕ) (hne : ps ≠ []) (d : ℤ) :
    kernelK_multi ps d =
      ∑ k ∈ Finset.range (ps.sum + 1), if (k : ℤ) ≤ d then kernelJump ps (k : ℤ) else 0 := by
  by_cases hd : d < 0
  · rw [kernelK_multi_neg ps d hd]
    symm
    apply Finset.sum_eq_zero
    intro k _
    have hk : ¬ ((k : ℤ) ≤ d) := by omega
    simp [hk]
  · have hd' : 0 ≤ d := by omega
    rw [kernelK_multi_telescope ps d hd']
    by_cases hs : d ≤ (ps.sum : ℤ)
    · have hm : d ≤ ((ps.sum + 1 : ℕ) : ℤ) - 1 := by rw [Nat.cast_add, Nat.cast_one]; omega
      rw [min_eq_right hm]
    · have hm : ((ps.sum + 1 : ℕ) : ℤ) - 1 ≤ d := by rw [Nat.cast_add, Nat.cast_one]; omega
      rw [min_eq_left hm]
      have h1 := kernelK_multi_large ps d hne (by omega)
      have h2 := kernelK_multi_large ps (((ps.sum + 1 : ℕ) : ℤ) - 1) hne
        (by rw [Nat.cast_add, Nat.cast_one]; omega)
      rw [h1, h2]

/-- The multi-generator quadratic form `Q(n) = ∑_{i,j ∈ G} K^(ps)(j − i) · n_i · n_j`. -/
@[expose] public noncomputable def quadFormMulti (ps : List ℕ) (G : Finset ℤ) (n : ℤ → ℝ) : ℝ :=
  ∑ i ∈ G, ∑ j ∈ G, (kernelK_multi ps (j - i) : ℝ) * n i * n j

/-- Tail pair-sum `T(s) = ∑_{i,j ∈ G, j − i ≥ s} n_i · n_j`. -/
@[expose] public noncomputable def pairTail (G : Finset ℤ) (n : ℤ → ℝ) (s : ℤ) : ℝ :=
  ∑ i ∈ G, ∑ j ∈ G, if s ≤ j - i then n i * n j else 0

/-- Breakpoints of `K^(ps)` as natural numbers in `[0, σ(ps)]`. -/
@[expose] public def breakpointSet (ps : List ℕ) : Finset ℕ :=
  (Finset.range (ps.sum + 1)).filter (fun k => kernelJump ps (k : ℤ) ≠ 0)

/-- The number of breakpoints is at most `σ(ps) + 1`. -/
public theorem breakpointSet_card_le (ps : List ℕ) : (breakpointSet ps).card ≤ ps.sum + 1 := by
  apply le_trans (Finset.card_filter_le _ _)
  simp

/-- Decomposition of the quadratic form over all positions `0 … σ`. -/
public theorem quadFormMulti_eq_range_sum (ps : List ℕ) (hne : ps ≠ [])
    (G : Finset ℤ) (n : ℤ → ℝ) :
    quadFormMulti ps G n =
      ∑ k ∈ Finset.range (ps.sum + 1), (kernelJump ps (k : ℤ) : ℝ) * pairTail G n (k : ℤ) := by
  unfold quadFormMulti pairTail
  have h : ∀ i j : ℤ, (kernelK_multi ps (j - i) : ℝ) =
      ∑ k ∈ Finset.range (ps.sum + 1),
        if (k : ℤ) ≤ j - i then (kernelJump ps (k : ℤ) : ℝ) else 0 := by
    intro i j
    rw [kernelK_multi_eq_sum_jump ps hne (j - i)]
    push_cast
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : (k : ℤ) ≤ j - i <;> simp [hk]
  calc ∑ i ∈ G, ∑ j ∈ G, (kernelK_multi ps (j - i) : ℝ) * n i * n j
      = ∑ i ∈ G, ∑ j ∈ G, ∑ k ∈ Finset.range (ps.sum + 1),
          (kernelJump ps (k : ℤ) : ℝ) * (if (k : ℤ) ≤ j - i then n i * n j else 0) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [h i j, Finset.sum_mul, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : (k : ℤ) ≤ j - i <;> simp [hk, mul_assoc]
    _ = ∑ i ∈ G, ∑ k ∈ Finset.range (ps.sum + 1), ∑ j ∈ G,
          (kernelJump ps (k : ℤ) : ℝ) * (if (k : ℤ) ≤ j - i then n i * n j else 0) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ k ∈ Finset.range (ps.sum + 1), ∑ i ∈ G, ∑ j ∈ G,
          (kernelJump ps (k : ℤ) : ℝ) * (if (k : ℤ) ≤ j - i then n i * n j else 0) :=
        Finset.sum_comm
    _ = ∑ k ∈ Finset.range (ps.sum + 1), (kernelJump ps (k : ℤ) : ℝ) *
          ∑ i ∈ G, ∑ j ∈ G, (if (k : ℤ) ≤ j - i then n i * n j else 0) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]

/-- **Breakpoint decomposition of the multi-generator quadratic form.**
`Q(n) = ∑_{s ∈ breakpoints of K^(ps)} π(s) · T(s)`, a sum with at most `σ(ps) + 1` terms. -/
public theorem quadFormMulti_eq_breakpoint_sum (ps : List ℕ) (hne : ps ≠ [])
    (G : Finset ℤ) (n : ℤ → ℝ) :
    quadFormMulti ps G n =
      ∑ k ∈ breakpointSet ps, (kernelJump ps (k : ℤ) : ℝ) * pairTail G n (k : ℤ) := by
  rw [quadFormMulti_eq_range_sum ps hne G n, breakpointSet]
  symm
  apply Finset.sum_filter_of_ne
  intro k _ hk hJ
  apply hk
  simp [hJ]

end LinearQ
