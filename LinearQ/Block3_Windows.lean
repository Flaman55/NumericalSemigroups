module

public import Mathlib
public import LinearQ.Block3_MultiGenerator

/-!
# Block 3b: Inclusion–exclusion form of K^(n), breakpoints and active windows

Connects the recursive kernel `kernelK_multi` (Block 3) to the definition used in the paper

  K^(n)(d) = ∑_{S ⊆ {p_1,…,p_n}} (-1)^{|S|} · 1_{d ≥ σ(S)},

and defines the active windows of K^(n) as intervals between consecutive breakpoints
(not as individual integer points).

* `kernelInclExcl`: the inclusion–exclusion sum over sub-multisets of the generators.
* `kernelK_multi_eq_inclExcl`: the recursive kernel equals the inclusion–exclusion sum.
* `kernelJump`: the parity function π(s) = K(s) − K(s−1), nonzero exactly at breakpoints.
* `activeWindowStarts`: left endpoints of the windows `[s, s')` on which K^(n) ≠ 0.
* `activeWindowCount_le_sigma`: w(n) ≤ σ(n).
-/

namespace LinearQ

/-- Inclusion–exclusion kernel over all sub-multisets `t` of the generator multiset `s`:
`∑_t (-1)^{|t|} · 1_{d ≥ σ(t)}`. -/
@[expose] public def kernelInclExcl (s : Multiset ℕ) (d : ℤ) : ℤ :=
  (s.powerset.map
    (fun t : Multiset ℕ =>
      (-1 : ℤ) ^ Multiset.card t * (if ((t.sum : ℕ) : ℤ) ≤ d then 1 else 0))).sum

/-- The recursive kernel `kernelK_multi` equals the inclusion–exclusion kernel over subsets of
the generators. -/
public theorem kernelK_multi_eq_inclExcl (ps : List ℕ) (d : ℤ) :
    kernelK_multi ps d = kernelInclExcl (ps : Multiset ℕ) d := by
  induction ps generalizing d with
  | nil =>
    simp [kernelInclExcl, kernelK_multi]
  | cons p ps ih =>
    have hc : ((p :: ps : List ℕ) : Multiset ℕ) = p ::ₘ (ps : Multiset ℕ) :=
      (Multiset.cons_coe p ps).symm
    have hterm : ∀ t : Multiset ℕ,
        (-1 : ℤ) ^ (Multiset.card t + 1) * (if ((p + t.sum : ℕ) : ℤ) ≤ d then 1 else 0)
          = (-1) * ((-1 : ℤ) ^ Multiset.card t * (if ((t.sum : ℕ) : ℤ) ≤ d - p then 1 else 0)) := by
      intro t
      by_cases h : ((t.sum : ℕ) : ℤ) ≤ d - p
      · have h' : ((p + t.sum : ℕ) : ℤ) ≤ d := by rw [Nat.cast_add]; omega
        simp only [h, h', ↓reduceIte, pow_succ]
        ring
      · have h' : ¬ (((p + t.sum : ℕ) : ℤ) ≤ d) := by rw [Nat.cast_add]; omega
        simp only [h, h', ↓reduceIte]
        ring
    rw [kernelK_multi_cons, ih d, ih (d - p), hc]
    simp only [kernelInclExcl, Multiset.powerset_cons, Multiset.map_add, Multiset.sum_add,
      Multiset.map_map, Function.comp_def, Multiset.card_cons, Multiset.sum_cons, hterm,
      Multiset.sum_map_mul_left]
    ring

/-- Parity function / jump of K^(ps) at `s`: `π(s) = K(s) − K(s−1)`. It is nonzero exactly at
the breakpoints of the step function `K^(ps)`. -/
@[expose] public def kernelJump (ps : List ℕ) (s : ℤ) : ℤ :=
  kernelK_multi ps s - kernelK_multi ps (s - 1)

/-- Left endpoints of the active windows of `K^(ps)`: breakpoints `s ∈ [0, σ)` at which
`K^(ps)` jumps to a nonzero value. The window starting at `s` is `[s, s')`, where `s'` is the
next breakpoint, and `K^(ps)` is constant and nonzero on it. -/
@[expose] public def activeWindowStarts (ps : List ℕ) : Finset ℤ :=
  (Finset.Ico (0 : ℤ) (ps.sum : ℤ)).filter
    (fun s => kernelJump ps s ≠ 0 ∧ kernelK_multi ps s ≠ 0)

/-- `w(ps)`: the number of active windows of `K^(ps)`. -/
@[expose] public def activeWindowCount (ps : List ℕ) : ℕ := (activeWindowStarts ps).card

/-- Every active window starts at an integer point of the support of `K^(ps)`, so the number
of active windows is at most the number of such points. -/
public theorem activeWindowCount_le_support (ps : List ℕ) :
    activeWindowCount ps ≤
      ((Finset.Ico (0 : ℤ) (ps.sum : ℤ)).filter (fun d => kernelK_multi ps d ≠ 0)).card := by
  apply Finset.card_le_card
  intro s hs
  simp only [activeWindowStarts, Finset.mem_filter] at hs ⊢
  exact ⟨hs.1, hs.2.2⟩

/-- `w(ps) ≤ σ(ps)`: the number of active windows is bounded by the sum of the generators. -/
public theorem activeWindowCount_le_sigma (ps : List ℕ) : activeWindowCount ps ≤ ps.sum := by
  apply le_trans (activeWindowCount_le_support ps)
  apply le_trans (Finset.card_filter_le _ _)
  rw [Int.card_Ico]
  simp

end LinearQ
