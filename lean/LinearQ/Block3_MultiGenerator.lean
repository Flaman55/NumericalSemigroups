import Mathlib
import LinearQ.Block1_KIntervals
import LinearQ.Block2_QReduction

/-!
# Block 3: Generalised kernel K^(n) for multiple generators

Recursive definition:
  K^([])(d)    = 1_{d ≥ 0}
  K^(p::ps)(d) = K^(ps)(d) - K^(ps)(d - p)
-/

namespace LinearQ

def kernelK_multi (ps : List ℕ) (d : ℤ) : ℤ :=
  match ps with
  | []      => if 0 ≤ d then 1 else 0
  | p :: ps => kernelK_multi ps d - kernelK_multi ps (d - p)

@[simp]
theorem kernelK_multi_nil (d : ℤ) :
    kernelK_multi [] d = if 0 ≤ d then 1 else 0 := rfl

@[simp]
theorem kernelK_multi_cons (p : ℕ) (ps : List ℕ) (d : ℤ) :
    kernelK_multi (p :: ps) d =
    kernelK_multi ps d - kernelK_multi ps (d - p) := rfl

/-- K^(ps) is zero for d < 0 -/
theorem kernelK_multi_neg (ps : List ℕ) (d : ℤ) (hd : d < 0) :
    kernelK_multi ps d = 0 := by
  induction ps generalizing d with
  | nil => simp; omega
  | cons p ps ih =>
    simp only [kernelK_multi_cons]
    linarith [ih d hd, ih (d - p) (by omega)]

/-- Single generator base: K^([p])(d) = 0 for d ≥ p -/
private lemma kernelK_single_large (p : ℕ) (d : ℤ) (hd : (p : ℤ) ≤ d) :
    kernelK_multi [p] d = 0 := by
  simp only [kernelK_multi_cons, kernelK_multi_nil]
  split_ifs <;> omega

/-- K^(ps) is zero for d ≥ σ(ps) when ps is nonempty -/
theorem kernelK_multi_large (ps : List ℕ) (d : ℤ)
    (hne : ps ≠ []) (hd : (ps.sum : ℤ) ≤ d) :
    kernelK_multi ps d = 0 := by
  induction ps generalizing d with
  | nil => exact absurd rfl hne
  | cons p ps ih =>
    simp only [kernelK_multi_cons, List.sum_cons, Nat.cast_add] at *
    have hp : (0 : ℤ) ≤ (p : ℤ) := Int.natCast_nonneg p
    have hps : (0 : ℤ) ≤ (ps.sum : ℤ) := Int.natCast_nonneg ps.sum
    have hd' : (p : ℤ) + (ps.sum : ℤ) ≤ d := by exact_mod_cast hd
    by_cases hnil : ps = []
    · subst hnil
      simp only [List.sum_nil, Nat.cast_zero, add_zero] at hd'
      simp only [kernelK_multi_nil]
      split_ifs with h <;> omega
    · linarith [ih d hnil (by linarith),
                ih (d - (p : ℤ)) hnil (by linarith)]

/-- Support of K^(ps) lies in [0, σ(ps)) for nonempty ps -/
theorem kernelK_multi_support (ps : List ℕ) (hne : ps ≠ []) (d : ℤ) :
    kernelK_multi ps d ≠ 0 → 0 ≤ d ∧ d < (ps.sum : ℤ) := by
  intro hd
  exact ⟨by_contra fun h => hd (kernelK_multi_neg ps d (by omega)),
         by_contra fun h => hd (kernelK_multi_large ps d hne (by omega))⟩

/-- K^([a, b]) agrees with kernelK a b -/
theorem kernelK_two_eq (a b : ℕ) (d : ℤ) :
    kernelK_multi [a, b] d = kernelK a b d := by
  simp only [kernelK_multi_cons, kernelK_multi_nil, kernelK]
  split_ifs <;> omega

/-- Incremental update -/
theorem kernelK_multi_add_gen (p : ℕ) (ps : List ℕ) (d : ℤ) :
    kernelK_multi (p :: ps) d =
    kernelK_multi ps d - kernelK_multi ps (d - ↑p) := rfl

/-- Support bound under generator addition -/
theorem kernelK_multi_support_bound (p : ℕ) (ps : List ℕ) (d : ℤ)
    (hne : kernelK_multi (p :: ps) d ≠ 0) :
    (kernelK_multi ps d ≠ 0) ∨ (kernelK_multi ps (d - p) ≠ 0) := by
  simp only [kernelK_multi_cons] at hne
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  simp [h1, h2] at hne

/-- w(ps) ≤ σ(ps): active window count bounded by generator sum -/
theorem w_le_sigma (ps : List ℕ) :
    ((Finset.Ico (0 : ℤ) (ps.sum : ℤ)).filter
      (fun d => kernelK_multi ps d ≠ 0)).card ≤ ps.sum := by
  apply le_trans (Finset.card_filter_le _ _)
  rw [Int.card_Ico]
  simp

end LinearQ
