import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-!
# Seminar 8
Mathlib: filters and limits

Based on: https://github.com/vasnesterov/public-2026-fall/blob/main/Shad/Lectures/lecture_3_analysis.lean
-/


/- Real numbers -/

#print Real
#print CauSeq.Completion.Cauchy
#check CauSeq.Completion.mk_eq

#synth Field ℝ
#synth LinearOrder ℝ
#synth IsStrictOrderedRing ℝ
#synth ConditionallyCompleteLinearOrder ℝ
#synth TopologicalSpace ℝ
#synth MetricSpace ℝ
#synth MeasurableSpace ℝ
-- etc


/- Arithmetic tactics -/

#check_failure (rfl : (2 : ℝ) + 2 = 4)

theorem real_arithmetic : (2 : ℝ) + 2 = 4 := by
  norm_num

#print axioms real_arithmetic

example (x y : ℝ) : (x - y) * (x + y) = x ^ 2 - y ^ 2 := by
  ring

example (x y : ℝ) (h₁ : x + 2 * y ≤ 3) (h₂ : 1 ≤ y) : x ≤ 1 := by
  linarith

example (x y : ℝ) : 2 * x * y ≤ x ^ 2 + y ^ 2 := by
  nlinarith [sq_nonneg (x - y)]

example (x : ℝ) : 0 < x ^ 2 + 1 := by
  positivity

example (x : ℝ) (hx : x ≠ 0) : (x + 1) / x = 1 + 1 / x := by
  field


/- Total functions, conditional laws -/

example : (1 : ℝ) / 0 = 0 := by simp
example : Real.sqrt (-1) = 0 := by norm_num

#check Real.sqrt_inj


/- Limits -/
open Filter Topology MeasureTheory

#check Filter
#check Tendsto
#check Tendsto (λ x : ℝ ↦ x / (x + 1)) atTop (𝓝 1)


/- Sets -/

#print Set
#print Set.Mem
#print Set.univ
#print Set.inter

/- Filters -/

#print Filter

#check (atTop : Filter ℕ)        -- n → +∞, sets containing a tail [N, ∞)
#check (atTop : Filter ℝ)        -- x → +∞
#check (atBot : Filter ℝ)        -- x → -∞
#check (𝓝 (2 : ℝ))              -- neighbourhoods of 2
#check (𝓝[≠] (2 : ℝ))           -- punctured neighbourhoods of 2
#check (𝓝[>] (0 : ℝ))           -- x → 0+: from the right
#check (𝓝[Set.Icc 0 1] (0 : ℝ)) -- x → 0 within [0, 1]
#check (𝓟 (Set.Icc (0 : ℝ) 1))  -- supersets of [0, 1]
#check (ae (volume : Measure ℝ)) -- sets with complement of measure zero

example {α : Type*} (s t : Set α) : t ∈ 𝓟 s ↔ s ⊆ t := Iff.rfl


/- Eventually and frequently -/

#print Filter.Eventually
#print Filter.Frequently

#check eventually_atTop
#check frequently_atTop
#check Metric.eventually_nhds_iff

example : ∀ᶠ n : ℕ in atTop, 100 < n := eventually_gt_atTop 100
example : ∀ᶠ x in 𝓝 (1 : ℝ), 0 < x := eventually_gt_nhds one_pos

example : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := Measure.ae_ne volume 0

example : ∃ᶠ n : ℕ in atTop, Even n := by
  rw [frequently_atTop]
  intro N
  exact ⟨2 * N, by omega, even_two_mul N⟩

example : ¬ ∀ᶠ n : ℕ in atTop, Even n := by
  rw [eventually_atTop]
  rintro ⟨N, hN⟩
  have h := hN (2 * N + 1) (by omega)
  simp at h

#check Filter.Eventually.and
#check Filter.Eventually.mono
#check Filter.Frequently.and_eventually

example {α : Type*} {l : Filter α} {p q : α → Prop}
    (hp : ∀ᶠ x in l, p x) (hq : ∀ᶠ x in l, q x) :
    ∀ᶠ x in l, p x ∧ q x := by
  filter_upwards [hp, hq] with x hx hy
  exact ⟨hx, hy⟩


/- Order and operations -/

example {α : Type*} (l₁ l₂ : Filter α) :
    l₁ ≤ l₂ ↔ ∀ s ∈ l₂, s ∈ l₁ := Iff.rfl

#synth CompleteLattice (Filter ℝ)

example (a : ℝ) (s : Set ℝ) : 𝓝[s] a = 𝓝 a ⊓ 𝓟 s := rfl
example (a : ℝ) (s : Set ℝ) : 𝓝[s] a ≤ 𝓝 a := inf_le_left

#check map

example {α β : Type*} (f : α → β) (l : Filter α) (s : Set β) :
    s ∈ map f l ↔ f ⁻¹' s ∈ l := Iff.rfl

#print Tendsto

example {α β : Type*} (f : α → β) (la : Filter α) (lb : Filter β) :
    Tendsto f la lb ↔ ∀ s ∈ lb, f ⁻¹' s ∈ la := Iff.rfl

#check map_mono

theorem tendsto_comp' {α β γ : Type*} {f : α → β} {g : β → γ}
    {la : Filter α} {lb : Filter β} {lc : Filter γ}
    (hg : Tendsto g lb lc) (hf : Tendsto f la lb) : Tendsto (g ∘ f) la lc := by
  unfold Tendsto at *
  rw [← map_map]
  exact le_trans (map_mono hf) hg

#check nhds_prod_eq
#check Tendsto.prodMk

theorem tendsto_add' {α M : Type*} [TopologicalSpace M] [Add M] [ContinuousAdd M]
    {l : Filter α} {f g : α → M} {a b : M}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) :
    Tendsto (λ x ↦ f x + g x) l (𝓝 (a + b)) := by
  have h₁ : Tendsto (λ x ↦ (f x, g x)) l (𝓝 a ×ˢ 𝓝 b) := hf.prodMk hg
  rw [← nhds_prod_eq] at h₁
  have h₂ : Tendsto (λ p : M × M ↦ p.1 + p.2) (𝓝 (a, b)) (𝓝 (a + b)) :=
    continuous_add.tendsto (a, b)
  exact tendsto_comp' h₂ h₁


/- Epsilon-delta -/

#check Metric.tendsto_atTop     -- ε-N
#check Metric.tendsto_nhds_nhds -- ε-δ

example (u : ℕ → ℝ) (a : ℝ) :
    Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |u n - a| < ε := by
  simp only [Metric.tendsto_atTop, Real.dist_eq]

example : Tendsto (λ n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, ?_⟩
  intro n hn
  rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
  apply (one_div_lt (by positivity) hε).2
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith


/- Using the library -/

#check tendsto_one_div_add_atTop_nhds_zero_nat
#check Tendsto.const_mul

example : Tendsto (λ n : ℕ ↦ 3 + 2 / ((n : ℝ) + 1)) atTop (𝓝 3) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h' := (h.const_mul 2).const_add 3
  simpa [div_eq_mul_inv] using h'

example : Tendsto (λ n : ℕ ↦ (n : ℝ) ^ 2) atTop atTop :=
  (tendsto_pow_atTop two_ne_zero).comp tendsto_natCast_atTop_atTop

example : Tendsto (λ x : ℝ ↦ x⁻¹) (𝓝[>] 0) atTop :=
  tendsto_inv_nhdsGT_zero


/- Squeeze theorem -/

#check tendsto_of_tendsto_of_tendsto_of_le_of_le'

example : Tendsto (λ n : ℕ ↦ Real.sin n / n) atTop (𝓝 0) := by
  have h₂ : Tendsto (λ n : ℕ ↦ 1 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have h₁ : Tendsto (λ n : ℕ ↦ -(1 / (n : ℝ))) atTop (𝓝 0) := by
    simpa using h₂.neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' h₁ h₂
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simpa only [neg_div] using
      div_le_div_of_nonneg_right (Real.neg_one_le_sin (n : ℝ)) hn'.le
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_le_div_of_nonneg_right (Real.sin_le_one (n : ℝ)) hn'.le


/- Uniqueness: which assumptions are really needed? -/

#check tendsto_nhds_unique
#synth T2Space ℝ
#print Filter.NeBot
#synth NeBot (atTop : Filter ℕ)

example {u : ℕ → ℝ} {a b : ℝ}
    (ha : Tendsto u atTop (𝓝 a)) (hb : Tendsto u atTop (𝓝 b)) : a = b :=
  tendsto_nhds_unique ha hb

example : (∅ : Set ℝ) ∈ (⊥ : Filter ℝ) := by simp
example (f : ℕ → ℝ) (a : ℝ) : Tendsto f ⊥ (𝓝 a) := tendsto_bot


/- Continuity -/

#print ContinuousAt
#check continuous_iff_continuousAt
#check Metric.continuous_iff

example : Continuous (λ x : ℝ ↦ Real.sin (x ^ 2) * Real.exp x + 1) := by
  fun_prop

example (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (λ x ↦ f (x ^ 3) - Real.cos (f x)) := by
  fun_prop

example {α : Type*} {l : Filter α} {u : α → ℝ} {a : ℝ}
    (hu : Tendsto u l (𝓝 a)) :
    Tendsto (λ x ↦ Real.sin (u x)) l (𝓝 (Real.sin a)) :=
  Real.continuous_sin.continuousAt.tendsto.comp hu


/-!
# Exercises
-/

section hw
  -- F(x, y) := x²y / (x⁴ + y²)
  noncomputable def F (p : ℝ × ℝ) : ℝ :=
    p.1 ^ 2 * p.2 / (p.1 ^ 4 + p.2 ^ 2)

  example (a b : ℝ) :
      Tendsto (λ t ↦ F (a * t, b * t)) (𝓝 0) (𝓝 0) := by
    sorry

  example : ¬ContinuousAt F (0, 0) := by
    sorry

  example :
      ¬ ∃ a : ℝ, Tendsto (λ n : ℕ ↦ Real.sin n) atTop (𝓝 a) := by
    sorry
end hw
