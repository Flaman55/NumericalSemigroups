import Mathlib

/-!
# Block 1: Kernel K and its interval structure

Central lemma: kernelK_spec gives the piecewise form directly.
All other results follow by case analysis on this spec.
-/

namespace LinearQ

/-- The kernel function K(d) = 1_{d≥0} - 1_{d≥a} - 1_{d≥b} + 1_{d≥a+b} -/
def kernelK (a b : ℕ) (d : ℤ) : ℤ :=
  (if (0 : ℤ) ≤ d then 1 else 0) -
  (if (a : ℤ) ≤ d then 1 else 0) -
  (if (b : ℤ) ≤ d then 1 else 0) +
  (if ((a : ℤ) + (b : ℤ)) ≤ d then 1 else 0)

/-- Central spec: piecewise form of K -/
lemma kernelK_spec (a b : ℕ) (hab : a < b) (d : ℤ) :
    kernelK a b d =
      if d < 0 then 0
      else if d < (a : ℤ) then 1
      else if d < (b : ℤ) then 0
      else if d < (a : ℤ) + b then -1
      else 0 := by
  have hlt : (a : ℤ) < b := Int.ofNat_lt.mpr hab
  simp only [kernelK]
  split_ifs <;> omega

/-- K is zero for negative d -/
theorem kernelK_neg (a b : ℕ) (d : ℤ) (hd : d < 0) :
    kernelK a b d = 0 := by
  simp only [kernelK]; split_ifs <;> omega

/-- K is zero for d ≥ a + b -/
theorem kernelK_large (a b : ℕ) (d : ℤ) (h : (a : ℤ) + b ≤ d) :
    kernelK a b d = 0 := by
  simp only [kernelK]; split_ifs <;> omega

/-- K = +1 on [0, a) -/
theorem kernelK_pos (a b : ℕ) (hab : a < b) (d : ℤ)
    (h0 : 0 ≤ d) (ha : d < (a : ℤ)) :
    kernelK a b d = 1 := by
  have hlt : (a : ℤ) < b := Int.ofNat_lt.mpr hab
  rw [kernelK_spec a b hab]
  simp only [not_lt.mpr h0, ↓reduceIte, ha, ↓reduceIte]

/-- K = 0 on [a, b) -/
theorem kernelK_zero_mid (a b : ℕ) (hab : a < b) (d : ℤ)
    (ha : (a : ℤ) ≤ d) (hb : d < (b : ℤ)) :
    kernelK a b d = 0 := by
  have hlt : (a : ℤ) < b := Int.ofNat_lt.mpr hab
  rw [kernelK_spec a b hab]
  simp only [show ¬d < 0 from by omega, ↓reduceIte,
             show ¬d < (a:ℤ) from by omega, ↓reduceIte, hb, ↓reduceIte]

/-- K = -1 on [b, a+b) -/
theorem kernelK_neg_mid (a b : ℕ) (hab : a < b) (d : ℤ)
    (hb : (b : ℤ) ≤ d) (hab2 : d < (a : ℤ) + b) :
    kernelK a b d = -1 := by
  have hlt : (a : ℤ) < b := Int.ofNat_lt.mpr hab
  rw [kernelK_spec a b hab]
  simp only [show ¬d < 0 from by omega, ↓reduceIte,
             show ¬d < (a:ℤ) from by omega, ↓reduceIte,
             show ¬d < (b:ℤ) from by omega, ↓reduceIte, hab2, ↓reduceIte]

/-- Master interval decomposition -/
theorem kernelK_intervals (a b : ℕ) (hab : a < b) (d : ℤ) :
    (d < 0 → kernelK a b d = 0) ∧
    (0 ≤ d → d < (a : ℤ) → kernelK a b d = 1) ∧
    ((a : ℤ) ≤ d → d < (b : ℤ) → kernelK a b d = 0) ∧
    ((b : ℤ) ≤ d → d < (a : ℤ) + b → kernelK a b d = -1) ∧
    ((a : ℤ) + b ≤ d → kernelK a b d = 0) :=
  ⟨kernelK_neg a b d,
   kernelK_pos a b hab d,
   kernelK_zero_mid a b hab d,
   kernelK_neg_mid a b hab d,
   kernelK_large a b d⟩

/-- K is supported on [0, a+b) -/
theorem kernelK_support (a b : ℕ) (hab : a < b) (d : ℤ) :
    kernelK a b d ≠ 0 → 0 ≤ d ∧ d < (a : ℤ) + b := by
  intro hne
  have hlt : (a : ℤ) < b := Int.ofNat_lt.mpr hab
  constructor
  · by_contra h
    exact hne (kernelK_neg a b d (by omega))
  · by_contra h
    exact hne (kernelK_large a b d (by omega))

/-- K nonzero implies membership in Finset.Ico -/
theorem kernelK_support_mem_Ico (a b : ℕ) (hab : a < b) (d : ℤ)
    (hne : kernelK a b d ≠ 0) :
    d ∈ Finset.Ico (0 : ℤ) ((a : ℤ) + b) := by
  simp only [Finset.mem_Ico]
  exact kernelK_support a b hab d hne

/-- K nonzero: either +1 on [0,a) or -1 on [b,a+b) -/
theorem kernelK_nonzero_intervals (a b : ℕ) (hab : a < b) (d : ℤ)
    (hne : kernelK a b d ≠ 0) :
    (0 ≤ d ∧ d < (a : ℤ) ∧ kernelK a b d = 1) ∨
    ((b : ℤ) ≤ d ∧ d < (a : ℤ) + b ∧ kernelK a b d = -1) := by
  have hlt : (a : ℤ) < b := Int.ofNat_lt.mpr hab
  have hsupp := kernelK_support a b hab d hne
  rw [kernelK_spec a b hab d] at hne ⊢
  split_ifs at hne ⊢ with h1 h2 h3 h4 <;> simp_all

end LinearQ
