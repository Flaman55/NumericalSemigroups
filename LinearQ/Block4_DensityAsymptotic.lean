module

public import Mathlib
public import Mathlib.Analysis.SpecificLimits.Basic
public import LinearQ.Block1_KIntervals
public import LinearQ.Block2_QReduction
public import LinearQ.Block3_MultiGenerator
public import LinearQ.Block3_Windows

/-!
# Block 4: Density asymptotic theorem (Theorem 5.2)

Goal: w(n) / (2^n - 1) = o(P(n)), equivalently δ(n)/P(n) → 1.

Proof strategy (matching the paper):
  Step 1: w(n) ≤ σ(n)              [Block 3b: activeWindowCount_le_sigma]
  Step 2: P(n) ≥ 1/(n+1)          [strict monotonicity → telescoping product]
  Step 3: σ(n)·(n+1)/(2^n-1) → 0  [subexponential growth: hsubexp]
  Step 4: squeeze                   [Steps 1–3]

Corollary: w(n)/(2^n-1) = o(P(n))  [Asymptotics.IsLittleO]

`GenSeq` models a strictly ordered sequence of generators ≥ 2 with
subexponential growth (log p(n)/n → 0). Strict monotonicity is the
natural hypothesis: it implies injectivity and the key bound p(k) ≥ k+2
(proved as a lemma, not assumed).
-/

namespace LinearQ

open Filter Topology Real Finset Asymptotics

/-! ## Generator sequence structure -/

/-- A strictly ordered generator sequence with subexponential growth.
    `hord` (StrictMono) is the canonical hypothesis: it implies injectivity
    and the lower bound p(k) ≥ k + 2 used in Step 2. -/
public structure GenSeq where
  p : ℕ → ℕ
  hge     : ∀ k, 2 ≤ p k
  hord    : StrictMono p
  hsubexp : Tendsto (fun n : ℕ => Real.log (p n) / (n : ℝ)) atTop (nhds 0)

variable (g : GenSeq)

/-! ## Derived properties of GenSeq -/

/-- Strict monotonicity implies injectivity. -/
public theorem GenSeq.injective : Function.Injective g.p :=
  g.hord.injective

/-- Key lower bound: the k-th generator is at least k + 2.
    Proof: induction on k using hge (base) and hord (step). -/
private lemma p_ge_idx_add_two (k : ℕ) : k + 2 ≤ g.p k := by
  induction k with
  | zero => exact g.hge 0
  | succ k ih =>
    -- g.hord gives g.p k < g.p (k + 1); combined with ih this closes the goal.
    -- Use (by omega) for k < k + 1 to keep the proof term in (· + 1) form.
    have hlt : g.p k < g.p (k + 1) := g.hord (by omega)
    omega

/-! ## Basic definitions -/

@[expose] public def prefixList (n : ℕ) : List ℕ := (List.range n).map g.p
@[expose] public def sigma (n : ℕ) : ℕ := (prefixList g n).sum

@[expose] public noncomputable def mertensProd (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (1 - 1 / (g.p k : ℝ))

/-- `w(n)`: the number of active windows of `K^(n)`, i.e. intervals between consecutive
breakpoints on which the kernel is nonzero (Block 3b). -/
@[expose] public def windowCount (n : ℕ) : ℕ := activeWindowCount (prefixList g n)

/-! ## Step 1: w(n) ≤ σ(n) -/

public theorem windowCount_le_sigma (n : ℕ) : windowCount g n ≤ sigma g n :=
  activeWindowCount_le_sigma (prefixList g n)

/-! ## Positivity of Mertens product -/

private lemma one_div_le_half (k : ℕ) : 1 / (g.p k : ℝ) ≤ 1 / 2 :=
  one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast g.hge k)

public theorem factor_ge_half (k : ℕ) : (1 / 2 : ℝ) ≤ 1 - 1 / (g.p k : ℝ) :=
  by linarith [one_div_le_half g k]

private lemma factor_pos (k : ℕ) : 0 < 1 - 1 / (g.p k : ℝ) :=
  lt_of_lt_of_le (by norm_num) (factor_ge_half g k)

public theorem mertensProd_pos (n : ℕ) : 0 < mertensProd g n :=
  Finset.prod_pos (fun k _ => factor_pos g k)

public theorem mertensProd_ge_half_pow (n : ℕ) : (1 / 2 : ℝ) ^ n ≤ mertensProd g n := by
  simp only [mertensProd]
  calc (1 / 2 : ℝ) ^ n
      = ∏ _k ∈ Finset.range n, (1 / 2 : ℝ) := by
          simp [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ k ∈ Finset.range n, (1 - 1 / (g.p k : ℝ)) :=
          Finset.prod_le_prod₀ (fun k _ => by norm_num) (fun k _ => factor_ge_half g k)

/-! ## Step 2: P(n) ≥ 1/(n+1) -/

/-- ∏_{k<n} (k+1)/(k+2) = 1/(n+1).
    Succ step: after div_mul_div_comm the form is 1*(n+1)/((n+1)*(n+2)) = 1/(n+1+1);
    cross-multiply via div_eq_div_iff and close with ring. -/
private lemma telescope_prod (n : ℕ) :
    ∏ k ∈ Finset.range n, ((k + 1 : ℝ) / (k + 2)) = 1 / (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    push_cast
    have h1 : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2 : (n : ℝ) + 2 ≠ 0 := by positivity
    rw [div_mul_div_comm, one_mul,
        div_eq_div_iff (mul_ne_zero h1 h2) (by positivity : (n : ℝ) + 1 + 1 ≠ 0)]
    ring

/-- P(n) ≥ 1/(n+1): compare factor-by-factor with the telescoping product.
    The bound p(k) ≥ k+2 (derived from StrictMono + hge) gives 1/p(k) ≤ 1/(k+2),
    hence each factor 1 − 1/p(k) ≥ (k+1)/(k+2). -/
public theorem mertensProd_ge_one_div_succ (n : ℕ) :
    1 / ((n : ℝ) + 1) ≤ mertensProd g n := by
  rw [← telescope_prod n]
  simp only [mertensProd]
  apply Finset.prod_le_prod₀
  · intro k _; positivity
  · intro k hk
    -- p(k) ≥ k+2 follows from StrictMono + hge (proved above)
    have h_ge : k + 2 ≤ g.p k := p_ge_idx_add_two g k
    -- rewrite (k+1)/(k+2) = 1 - 1/(k+2) for easy comparison
    have h_frac : ((k : ℝ) + 1) / ((k : ℝ) + 2) = 1 - 1 / ((k : ℝ) + 2) := by
      field_simp; ring
    rw [h_frac]
    simp only [sub_le_sub_iff_left]
    apply one_div_le_one_div_of_le
    · positivity
    · exact_mod_cast h_ge

/-! ## Step 3: σ(n)·(n+1)/(2^n-1) → 0 -/

/-- Step A: hsubexp implies p(k) eventually grows slower than (6/5)^k.
    For large k, log(p k)/k < log(6/5), hence p(k) < (6/5)^k. -/
private lemma p_eventually_le_pow (g : GenSeq) :
    ∀ᶠ k in atTop, (g.p k : ℝ) ≤ (6/5 : ℝ) ^ k := by
  have hlog_pos : (0 : ℝ) < Real.log (6/5 : ℝ) := Real.log_pos (by norm_num)
  have hlt : ∀ᶠ k in atTop, Real.log (↑(g.p k)) / (k : ℝ) < Real.log (6/5 : ℝ) :=
    g.hsubexp.eventually (Iio_mem_nhds hlog_pos) |>.mono (fun k hk => Set.mem_Iio.mp hk)
  filter_upwards [hlt, eventually_ge_atTop 1] with k hk hk1
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hlog_ineq : Real.log (g.p k) < Real.log ((6/5 : ℝ) ^ k) := by
    rw [Real.log_pow]
    -- log(p k)/k < log(6/5), so log(p k) < k · log(6/5) = log((6/5)^k)
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
    have hmul := mul_lt_mul_of_pos_right hk hkR
    rwa [div_mul_cancel₀ _ hkne, mul_comm (Real.log (6/5 : ℝ)) (k : ℝ)] at hmul
  -- p(k) ≥ (6/5)^k would give log(p k) ≥ log((6/5)^k), contradicting hlog_ineq
  by_contra h
  simp only [not_le] at h
  exact absurd hlog_ineq (not_lt.mpr
    (Real.log_le_log (by positivity : (0:ℝ) < (6/5:ℝ)^k) h.le))

/-- σ(n+1) = σ(n) + p(n): unfolding the prefix sum by one step. -/
private lemma sigma_succ (g : GenSeq) (n : ℕ) :
    sigma g (n + 1) = sigma g n + g.p n := by
  unfold sigma prefixList
  simp [List.range_succ, List.map_append, List.sum_append]

/-- σ is monotone: longer prefix sums are larger. -/
private lemma sigma_mono (g : GenSeq) {m n : ℕ} (h : m ≤ n) :
    sigma g m ≤ sigma g n := by
  induction n with
  | zero => simp [Nat.le_zero.mp h]
  | succ n ih =>
    rcases Nat.eq_or_lt_of_le h with rfl | h'
    · exact le_refl _
    · have hle : sigma g m ≤ sigma g n := ih (Nat.lt_succ_iff.mp h')
      have hstep : sigma g n ≤ sigma g (n + 1) := by
        have := sigma_succ g n; omega
      omega

/-- Step B: σ(n) ≤ C + 5·(6/5)^n for some constant C ≥ 0.
    Past the threshold N where p(k) ≤ (6/5)^k, each new term contributes
    at most (6/5)^k, giving a geometric series bound; below N the sum is
    bounded by the constant σ(N). -/
private lemma sigma_le_const_add_geom (g : GenSeq) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, (sigma g n : ℝ) ≤ C + 5 * (6/5 : ℝ) ^ n := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (p_eventually_le_pow g)
  refine ⟨(sigma g N : ℝ), by exact_mod_cast Nat.zero_le _, fun n => ?_⟩
  induction n with
  | zero =>
    have h0 : (sigma g 0 : ℝ) = 0 := by simp [sigma, prefixList]
    rw [h0]
    linarith [show (0 : ℝ) ≤ (sigma g N : ℝ) from by exact_mod_cast Nat.zero_le _,
              show (0 : ℝ) < 5 * (6/5 : ℝ) ^ 0 from by norm_num]
  | succ n ih =>
    rcases Nat.lt_or_ge N (n + 1) with h | h
    · -- N < n+1, so N ≤ n: use IH and the pointwise bound hN
      have hn : N ≤ n := Nat.lt_succ_iff.mp h
      have hpn : (g.p n : ℝ) ≤ (6/5 : ℝ) ^ n := hN n hn
      have hsucc : (sigma g (n + 1) : ℝ) = (sigma g n : ℝ) + (g.p n : ℝ) :=
        by exact_mod_cast sigma_succ g n
      rw [hsucc]
      calc (sigma g n : ℝ) + (g.p n : ℝ)
          ≤ ((sigma g N : ℝ) + 5 * (6/5 : ℝ) ^ n) + (6/5 : ℝ) ^ n := by linarith [ih]
        _ = (sigma g N : ℝ) + 5 * (6/5 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring
    · -- n+1 ≤ N: σ(n+1) ≤ σ(N) = C
      have hmono : sigma g (n + 1) ≤ sigma g N := sigma_mono g h
      linarith [show (0 : ℝ) ≤ 5 * (6/5 : ℝ) ^ (n + 1) from by positivity,
               show (sigma g (n + 1) : ℝ) ≤ (sigma g N : ℝ) from by exact_mod_cast hmono]

/-- Step C: σ(n)·(n+1)/(2^n-1) → 0.

    Factor the expression as f₁·f₂·f₃:
      f₁ n = σ(n) / (3/2)^n       → 0  (Steps A–B + squeeze: C·(2/3)^n + 5·(4/5)^n)
      f₂ n = (n+1) · (3/4)^n      → 0  (linear envelope of a geometric series)
      f₃ n = 2^n / (2^n − 1)      → 1  (ratio of two geometric sequences)

    The key identity 1.5 · 0.75 / 2 = 9/16 · 2/9 · ... simplifies to
    f₁ · f₂ · f₃ = σ(n)·(n+1)/(2^n−1). The squeeze in f₁ works because
    (6/5)/(3/2) = 4/5 < 1, so σ(n)/(3/2)^n → 0. -/
public theorem sigma_succ_div_pow_tendsto :
    Tendsto (fun n : ℕ => (sigma g n : ℝ) * ((n : ℝ) + 1) / ((2 : ℝ) ^ n - 1))
    atTop (nhds 0) := by
  -- 1. Auxiliary function definitions
  let f1 := fun n : ℕ => (sigma g n : ℝ) / (1.5 : ℝ) ^ n
  let f2 := fun n : ℕ => ((n : ℝ) + 1) * (0.75 : ℝ) ^ n
  let f3 := fun n : ℕ => (2 : ℝ) ^ n / ((2 : ℝ) ^ n - 1)
  -- 2. Algebraic identity: f₁·f₂·f₃ = σ(n)·(n+1)/(2^n−1)
  have h_eq : (fun n => f1 n * f2 n * f3 n) =ᶠ[atTop]
  (fun n => (sigma g n : ℝ) * ((n : ℝ) + 1) / ((2 : ℝ) ^ n - 1)) := by
    apply eventually_atTop.mpr
    use 1
    intro n hn
    dsimp [f1, f2, f3]
    have h_den_nz : (2 : ℝ) ^ n - 1 ≠ 0 := by
      have h_pow : (2 : ℝ) ^ 0 < (2 : ℝ) ^ n := pow_lt_pow_right₀ (by norm_num) (by omega)
      norm_num at h_pow; linarith
    rw [show (1.5 : ℝ) = 3/2 by norm_num, show (0.75 : ℝ) = 3/4 by norm_num]
    field_simp [h_den_nz]
    simp only [div_pow]
    rw [show (4 : ℝ) = 2^2 by norm_num, ← pow_mul, mul_comm 2 n, pow_mul]
    field_simp [h_den_nz]
  -- 3. Replace the target with the factored form
  apply Tendsto.congr' h_eq
  -- 4. Individual limits
  have h1 : Tendsto f1 atTop (nhds 0) := by
    -- Squeeze: 0 ≤ σ(n)/(3/2)^n ≤ C·(2/3)^n + 5·(4/5)^n → 0.
    -- The upper bound holds because (4/5)^n = (6/5)^n / (3/2)^n.
    obtain ⟨C, hC, hbound⟩ := sigma_le_const_add_geom g
    apply squeeze_zero
    · -- f₁ n ≥ 0: σ(n) ≥ 0 and (3/2)^n > 0
      intro n
      apply div_nonneg (by exact_mod_cast Nat.zero_le _)
      positivity
    · -- f₁ n ≤ C·(2/3)^n + 5·(4/5)^n
      intro n
      change (sigma g n : ℝ) / (1.5 : ℝ) ^ n ≤ C * (2/3 : ℝ) ^ n + 5 * (4/5 : ℝ) ^ n
      rw [show (1.5 : ℝ) = 3/2 from by norm_num]
      have hden_pos : (0 : ℝ) < (3/2 : ℝ) ^ n := by positivity
      have hone : (2/3 : ℝ) ^ n * (3/2 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
      have hsix : (4/5 : ℝ) ^ n * (3/2 : ℝ) ^ n = (6/5 : ℝ) ^ n := by rw [← mul_pow]; norm_num
      have hprod : (C * (2/3 : ℝ) ^ n + 5 * (4/5 : ℝ) ^ n) * (3/2 : ℝ) ^ n =
                   C + 5 * (6/5 : ℝ) ^ n := by
        calc (C * (2/3 : ℝ) ^ n + 5 * (4/5 : ℝ) ^ n) * (3/2 : ℝ) ^ n
            = C * ((2/3 : ℝ) ^ n * (3/2 : ℝ) ^ n) + 5 * ((4/5 : ℝ) ^ n * (3/2 : ℝ) ^ n) := by ring
          _ = C + 5 * (6/5 : ℝ) ^ n := by rw [hone, hsix]; ring
      have hle : (sigma g n : ℝ) ≤
                 (C * (2/3 : ℝ) ^ n + 5 * (4/5 : ℝ) ^ n) * (3/2 : ℝ) ^ n :=
        hprod.symm ▸ hbound n
      have inv_nn : (0 : ℝ) ≤ ((3/2 : ℝ) ^ n)⁻¹ := inv_nonneg.mpr hden_pos.le
      calc (sigma g n : ℝ) / (3/2 : ℝ) ^ n
          ≤ ((C * (2/3 : ℝ) ^ n + 5 * (4/5 : ℝ) ^ n) * (3/2 : ℝ) ^ n) / (3/2 : ℝ) ^ n := by
            simp only [div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_right hle inv_nn
        _ = C * (2/3 : ℝ) ^ n + 5 * (4/5 : ℝ) ^ n :=
            mul_div_cancel_right₀ _ (ne_of_gt hden_pos)
    · -- C·(2/3)^n + 5·(4/5)^n → 0
      have hC23 : Tendsto (fun n : ℕ => C * (2/3 : ℝ) ^ n) atTop (nhds 0) := by
        simpa [mul_zero] using tendsto_const_nhds.mul
          (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(2/3 : ℝ)| < 1))
      have h45 : Tendsto (fun n : ℕ => 5 * (4/5 : ℝ) ^ n) atTop (nhds 0) := by
        simpa [mul_zero] using tendsto_const_nhds.mul
          (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(4/5 : ℝ)| < 1))
      simpa using hC23.add h45
  have h2 : Tendsto f2 atTop (nhds 0) := by
    dsimp [f2]
    -- (n+1)·r^n = n·r^n + r^n; both are tail-summable, so each term → 0.
    have hr_norm : ‖(0.75 : ℝ)‖ < 1 := by norm_num
    have hA : Summable (fun n : ℕ => (n : ℝ) * (0.75 : ℝ) ^ n) :=
      (hasSum_coe_mul_geometric_of_norm_lt_one hr_norm).summable
    have hB : Summable (fun n : ℕ => (0.75 : ℝ) ^ n) :=
      summable_geometric_of_abs_lt_one (by norm_num)
    have heq : (fun n : ℕ => ((n : ℝ) + 1) * (0.75 : ℝ) ^ n) =
               (fun n : ℕ => (n : ℝ) * (0.75 : ℝ) ^ n + (0.75 : ℝ) ^ n) := by
      ext n; ring
    rw [heq]
    exact (hA.add hB).tendsto_atTop_zero
  have h3 : Tendsto f3 atTop (nhds 1) := by
    dsimp [f3]
    have hpow :
        Tendsto (fun n : ℕ => ((2 : ℝ) ^ n - 1) / (2 : ℝ) ^ n)
          atTop
          (nhds 1) := by
      have h_aux :
          (fun n : ℕ => (((2 : ℝ) ^ n - 1) / (2 : ℝ) ^ n))
            =
          (fun n : ℕ => 1 - (1 / (2 : ℝ) ^ n)) := by
        ext n
        have hne : ((2 : ℝ) ^ n) ≠ 0 := by positivity
        field_simp [hne]
      rw [h_aux]
      have h_zero :
          Tendsto (fun n : ℕ => (1 : ℝ) / (2 : ℝ) ^ n)
            atTop
            (nhds 0) := by
        simpa [one_div]
          using
            (tendsto_pow_atTop_nhds_zero_of_abs_lt_one
              (by norm_num : |(1 / 2 : ℝ)| < 1))
      simpa using tendsto_const_nhds.sub h_zero
    -- Invert the limit: ((2^n-1)/2^n)⁻¹ = 2^n/(2^n-1) = f₃ n, and 1⁻¹ = 1.
    have h_inv := hpow.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa [inv_div, inv_one] using h_inv
  -- 5. Combine limits: f₁·(f₂·f₃) → 0·(0·1) = 0
  have h23 :
      Tendsto (fun n => f2 n * f3 n)
        atTop
        (nhds (0 * 1)) := by
    exact h2.mul h3
  have h123 :
      Tendsto (fun n => f1 n * (f2 n * f3 n))
        atTop
        (nhds (0 * (0 * 1))) := by
    exact h1.mul h23
  convert h123 using 1
  · ext n
    ring
  · norm_num

/-! ## Step 4: density ratio → 0 -/

public theorem density_ratio_tendsto :
    Tendsto (fun n : ℕ =>
      (windowCount g n : ℝ) / ((2 ^ n - 1) * mertensProd g n))
    atTop (nhds 0) := by
  have hM_pos : ∀ n : ℕ, 0 < mertensProd g n := mertensProd_pos g
  have hM_lb  : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ mertensProd g n :=
    mertensProd_ge_one_div_succ g
  have hw_le  : ∀ n : ℕ, (windowCount g n : ℝ) ≤ (sigma g n : ℝ) := fun n => by
    exact_mod_cast windowCount_le_sigma g n
  have h_lb : ∀ n : ℕ,
      (0 : ℝ) ≤ (windowCount g n : ℝ) / ((2 ^ n - 1) * mertensProd g n) := by
    intro n
    apply div_nonneg (by exact_mod_cast Nat.zero_le _)
    apply mul_nonneg
    · linarith [show (1 : ℝ) ≤ (2 : ℝ) ^ n from by
          exact_mod_cast (Nat.one_le_two_pow (n := n))]
    · exact le_of_lt (hM_pos n)
  have h_ub : ∀ n : ℕ,
      (windowCount g n : ℝ) / ((2 ^ n - 1) * mertensProd g n) ≤
      (sigma g n : ℝ) * ((n : ℝ) + 1) / ((2 : ℝ) ^ n - 1) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [windowCount, activeWindowCount, activeWindowStarts, sigma, prefixList]
    · have hMn  : 0 < mertensProd g n   := hM_pos n
      have hMlb : 1 / ((n : ℝ) + 1) ≤ mertensProd g n := hM_lb n
      have hn1  : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hw   : (windowCount g n : ℝ) ≤ (sigma g n : ℝ) := hw_le n
      have hsg  : (0 : ℝ) ≤ (sigma g n : ℝ) := by exact_mod_cast Nat.zero_le _
      have h2n_lt : 1 < 2 ^ n :=
        calc (1 : ℕ) < 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n            := Nat.pow_le_pow_right (by norm_num) hn
      have h2n1 : (0 : ℝ) < (2 : ℝ) ^ n - 1 := by
        linarith [show (1 : ℝ) < (2 : ℝ) ^ n from by exact_mod_cast h2n_lt]
      have hM1 : (1 : ℝ) ≤ ((n : ℝ) + 1) * mertensProd g n :=
        calc (1 : ℝ) = ((n : ℝ) + 1) * (1 / ((n : ℝ) + 1)) := by field_simp
          _ ≤ ((n : ℝ) + 1) * mertensProd g n :=
              mul_le_mul_of_nonneg_left hMlb (le_of_lt hn1)
      -- Key bound: w(n) ≤ σ(n)·(n+1)·P(n), from w ≤ σ and 1 ≤ (n+1)·P(n)
      have h3 : (windowCount g n : ℝ) ≤
                (sigma g n : ℝ) * ((n : ℝ) + 1) * mertensProd g n := by
        nlinarith [mul_le_mul_of_nonneg_left hM1 hsg]
      have hpos : (0 : ℝ) < ((2 : ℝ) ^ n - 1) * mertensProd g n := mul_pos h2n1 hMn
      -- Divide both sides by (2^n-1)·P(n); P(n) cancels on the right
      calc (windowCount g n : ℝ) / (((2 : ℝ) ^ n - 1) * mertensProd g n)
          ≤ (sigma g n : ℝ) * ((n : ℝ) + 1) * mertensProd g n /
            (((2 : ℝ) ^ n - 1) * mertensProd g n) := by
              simp only [div_eq_mul_inv]
              exact mul_le_mul_of_nonneg_right h3 (inv_nonneg.mpr hpos.le)
        _ = (sigma g n : ℝ) * ((n : ℝ) + 1) / ((2 : ℝ) ^ n - 1) := by
              field_simp [hMn.ne', h2n1.ne']
  exact squeeze_zero h_lb h_ub (sigma_succ_div_pow_tendsto g)

/-! ## Corollary: δ(n)/P(n) → 1 -/

/-- Main theorem (Theorem 5.2): the density defect ratio tends to 1.
    Equivalently: w(n)/(2^n-1) is asymptotically negligible relative to P(n). -/
public theorem gap_div_mertens_tendsto_one :
    Tendsto (fun n : ℕ =>
      (mertensProd g n - (windowCount g n : ℝ) / (2 ^ n - 1)) /
      mertensProd g n)
    atTop (nhds 1) := by
  have hrat := density_ratio_tendsto g
  have hfun : ∀ n : ℕ,
      (mertensProd g n - (windowCount g n : ℝ) / (2 ^ n - 1)) / mertensProd g n =
      1 - (windowCount g n : ℝ) / ((2 ^ n - 1) * mertensProd g n) := by
    intro n
    -- (P - w/D) / P = P/P - (w/D)/P = 1 - w/(D·P); no case split needed
    rw [sub_div, div_self (mertensProd_pos g n).ne', div_div]
  simp_rw [hfun]
  have h1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) := tendsto_const_nhds
  simpa only [sub_zero] using h1.sub hrat

/-! ## Landau notation: w(n)/(2^n-1) = o(P(n)) -/

/-- Formal Landau corollary: the window count density is little-o of the
    Mertens product. This is the standard asymptotic statement of Theorem 5.2. -/
public theorem windowCount_isLittleO_mertensProd :
    (fun n : ℕ => (windowCount g n : ℝ) / ((2 : ℝ) ^ n - 1)) =o[atTop] (mertensProd g) := by
  apply isLittleO_of_tendsto
  · -- vacuous: P(n) > 0 always, so the antecedent P(n) = 0 never fires
    intro n hn
    exact absurd hn (mertensProd_pos g n).ne'
  · -- (w(n)/(2^n-1)) / P(n) = w(n)/((2^n-1)·P(n)) → 0
    have heq : (fun n : ℕ =>
        (windowCount g n : ℝ) / ((2 : ℝ) ^ n - 1) / mertensProd g n) =
        (fun n : ℕ =>
        (windowCount g n : ℝ) / (((2 : ℝ) ^ n - 1) * mertensProd g n)) := by
      -- div_div: a / b / c = a / (b * c); ring cannot close this (inverse identity)
      ext n; rw [div_div]
    rw [heq]
    exact density_ratio_tendsto g

end LinearQ
