module

public import LinearQ

/-!
# Proved solutions

This module defines exactly the same objects as `Challenge.lean` and proves each advertised
statement. The proofs are thin wrappers around the development in `LinearQ/`: the
inclusion–exclusion kernel defined here is shown equal to the recursive kernel
`LinearQ.kernelK_multi` (`LinearQ.kernelK_multi_eq_inclExcl`), and the statements follow from
`LinearQ.quadForm_eq_linearForm` (Block 2), `LinearQ.activeWindowCount_le_sigma` (Block 3b),
`LinearQ.quadFormMulti_eq_breakpoint_sum` (Block 5), and the density theorems of Block 4.
-/

/-- The generalised kernel `K⁽ⁿ⁾(d) = ∑_S (-1)^{|S|} · 𝟙_{d ≥ σ(S)}`, summed over all
sub-multisets `S` of the generator list `ps` (so repeated generators are counted with
multiplicity, as index subsets). -/
@[expose] public def Submission.kernel (ps : List ℕ) (d : ℤ) : ℤ :=
  (((ps : Multiset ℕ).powerset).map
    (fun t : Multiset ℕ =>
      (-1 : ℤ) ^ Multiset.card t * (if ((t.sum : ℕ) : ℤ) ≤ d then 1 else 0))).sum

/-- The jump (parity function) of the kernel at `s`: `π(s) = K(s) − K(s−1)`. It is nonzero
exactly at the breakpoints of the step function `K`. -/
@[expose] public def Submission.jump (ps : List ℕ) (s : ℤ) : ℤ :=
  Submission.kernel ps s - Submission.kernel ps (s - 1)

/-- `w(ps)`: the number of active windows of the kernel. Windows are the intervals
`[s, s')` between consecutive breakpoints; the window starting at the breakpoint `s ∈ [0, σ)` is
active when the kernel is nonzero on it. Windows are counted by their left endpoints. -/
@[expose] public def Submission.activeWindowCount (ps : List ℕ) : ℕ :=
  ((Finset.Ico (0 : ℤ) (ps.sum : ℤ)).filter
    (fun s => Submission.jump ps s ≠ 0 ∧ Submission.kernel ps s ≠ 0)).card

/-- The quadratic form `Q(n) = ∑_{i,j ∈ G} K⁽ⁿ⁾(j − i) · nᵢ · nⱼ`. -/
@[expose] public noncomputable def Submission.quadForm
    (ps : List ℕ) (G : Finset ℤ) (n : ℤ → ℝ) : ℝ :=
  ∑ i ∈ G, ∑ j ∈ G, (Submission.kernel ps (j - i) : ℝ) * n i * n j

/-- The tail pair-sum `T(s) = ∑_{i,j ∈ G, j − i ≥ s} nᵢ nⱼ`. -/
@[expose] public noncomputable def Submission.pairTail
    (G : Finset ℤ) (n : ℤ → ℝ) (s : ℤ) : ℝ :=
  ∑ i ∈ G, ∑ j ∈ G, if s ≤ j - i then n i * n j else 0

/-- The breakpoints of the kernel, as natural numbers in `[0, σ]`. -/
@[expose] public def Submission.breakpoints (ps : List ℕ) : Finset ℕ :=
  (Finset.range (ps.sum + 1)).filter (fun k => Submission.jump ps (k : ℤ) ≠ 0)

/-- The sliding-window form for two generators `a < b`:
`∑_{k ∈ G} n_k (W⁺_k − W⁻_k)`, where `W⁺_k = ∑_{j ∈ G, k ≤ j < k + a} n_j` and
`W⁻_k = ∑_{j ∈ G, k + b ≤ j < k + a + b} n_j`. -/
@[expose] public noncomputable def Submission.linearForm2
    (a b : ℕ) (G : Finset ℤ) (n : ℤ → ℝ) : ℝ :=
  ∑ k ∈ G, n k *
    ((∑ j ∈ G, if k ≤ j ∧ j < k + (a : ℤ) then n j else 0) -
      (∑ j ∈ G, if k + (b : ℤ) ≤ j ∧ j < k + (a : ℤ) + b then n j else 0))

/-- The density product `P(n) = ∏_{k<n} (1 − 1/pₖ)`. -/
@[expose] public noncomputable def Submission.mertensProd (p : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (1 - 1 / (p k : ℝ))

/-- The inclusion–exclusion kernel of this file equals the recursive kernel of `LinearQ`. -/
public theorem Submission.kernel_eq (ps : List ℕ) (d : ℤ) :
    Submission.kernel ps d = LinearQ.kernelK_multi ps d :=
  (LinearQ.kernelK_multi_eq_inclExcl ps d).symm

/-- The jump of this file equals the jump of `LinearQ`. -/
public theorem Submission.jump_eq (ps : List ℕ) (s : ℤ) :
    Submission.jump ps s = LinearQ.kernelJump ps s := by
  simp only [Submission.jump, LinearQ.kernelJump, Submission.kernel_eq]

/-- The window count of this file equals the window count of `LinearQ`. -/
public theorem Submission.activeWindowCount_eq (ps : List ℕ) :
    Submission.activeWindowCount ps = LinearQ.activeWindowCount ps := by
  simp only [Submission.activeWindowCount, LinearQ.activeWindowCount,
    LinearQ.activeWindowStarts, Submission.jump_eq, Submission.kernel_eq]

public theorem Submission.quadForm_two_eq_linearForm2 (a b : ℕ) (hab : a < b)
    (G : Finset ℤ) (n : ℤ → ℝ) :
    Submission.quadForm [a, b] G n = Submission.linearForm2 a b G n := by
  have h := LinearQ.quadForm_eq_linearForm a b hab G n
  have hk : ∀ d : ℤ, Submission.kernel [a, b] d = LinearQ.kernelK a b d := fun d => by
    rw [Submission.kernel_eq]
    exact LinearQ.kernelK_two_eq a b d
  simp only [Submission.quadForm, hk]
  exact h

public theorem Submission.quadForm_eq_breakpoint_sum (ps : List ℕ) (hne : ps ≠ [])
    (G : Finset ℤ) (n : ℤ → ℝ) :
    Submission.quadForm ps G n =
      ∑ k ∈ Submission.breakpoints ps,
        (Submission.jump ps (k : ℤ) : ℝ) * Submission.pairTail G n (k : ℤ) := by
  have h := LinearQ.quadFormMulti_eq_breakpoint_sum ps hne G n
  simpa only [Submission.quadForm, Submission.breakpoints, Submission.pairTail,
    Submission.jump_eq, Submission.kernel_eq, LinearQ.quadFormMulti, LinearQ.breakpointSet,
    LinearQ.pairTail] using h

public theorem Submission.breakpoints_card_le (ps : List ℕ) :
    (Submission.breakpoints ps).card ≤ ps.sum + 1 := by
  have h := LinearQ.breakpointSet_card_le ps
  simpa only [Submission.breakpoints, LinearQ.breakpointSet, Submission.jump_eq] using h

public theorem Submission.activeWindowCount_le_sigma (ps : List ℕ) :
    Submission.activeWindowCount ps ≤ ps.sum := by
  rw [Submission.activeWindowCount_eq]
  exact LinearQ.activeWindowCount_le_sigma ps

public theorem Submission.windowCount_isLittleO_mertensProd
    (p : ℕ → ℕ) (hge : ∀ k, 2 ≤ p k) (hord : StrictMono p)
    (hsub : Filter.Tendsto (fun n : ℕ => Real.log (p n) / (n : ℝ)) Filter.atTop (nhds 0)) :
    Asymptotics.IsLittleO Filter.atTop
      (fun n : ℕ =>
        (Submission.activeWindowCount ((List.range n).map p) : ℝ) / ((2 : ℝ) ^ n - 1))
      (Submission.mertensProd p) := by
  let g : LinearQ.GenSeq := ⟨p, hge, hord, hsub⟩
  have h := LinearQ.windowCount_isLittleO_mertensProd g
  have heq : (fun n : ℕ =>
        (Submission.activeWindowCount ((List.range n).map p) : ℝ) / ((2 : ℝ) ^ n - 1))
      = (fun n : ℕ => (LinearQ.windowCount g n : ℝ) / ((2 : ℝ) ^ n - 1)) := by
    funext n
    rw [Submission.activeWindowCount_eq]
    rfl
  rw [heq]
  exact h

public theorem Submission.gap_div_mertensProd_tendsto_one
    (p : ℕ → ℕ) (hge : ∀ k, 2 ≤ p k) (hord : StrictMono p)
    (hsub : Filter.Tendsto (fun n : ℕ => Real.log (p n) / (n : ℝ)) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n : ℕ =>
        (Submission.mertensProd p n -
          (Submission.activeWindowCount ((List.range n).map p) : ℝ) / (2 ^ n - 1)) /
          Submission.mertensProd p n)
      Filter.atTop (nhds 1) := by
  let g : LinearQ.GenSeq := ⟨p, hge, hord, hsub⟩
  have h := LinearQ.gap_div_mertens_tendsto_one g
  have heq : (fun n : ℕ =>
        (Submission.mertensProd p n -
          (Submission.activeWindowCount ((List.range n).map p) : ℝ) / (2 ^ n - 1)) /
          Submission.mertensProd p n)
      = (fun n : ℕ =>
        (LinearQ.mertensProd g n - (LinearQ.windowCount g n : ℝ) / (2 ^ n - 1)) /
          LinearQ.mertensProd g n) := by
    funext n
    rw [Submission.activeWindowCount_eq]
    rfl
  rw [heq]
  exact h
