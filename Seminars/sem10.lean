import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.Tactic.Module

/-!
# Seminar 10
Linear maps on generators and bases.
-/

namespace Seminar10

/- Complex numbers -/

section
  open Complex
  open scoped ComplexConjugate

  #print Complex
  #synth Field ℂ

  example (a : ℝ) : (a : ℂ) = ⟨a, 0⟩ := rfl
  example (z w : ℂ) : (z * w).re = z.re * w.re - z.im * w.im := rfl

  #print Complex.I
  example : I ^ 2 = -1 := I_sq
  example (a b : ℝ) : (⟨a, b⟩ : ℂ) = a + b * I := by
    apply Complex.ext <;> simp

  #check (conj : ℂ →+* ℂ)
  example (z : ℂ) : conj z = ⟨z.re, -z.im⟩ := rfl
  example (a b : ℝ) : conj (a + b * I) = a - b * I := by
    simp [sub_eq_add_neg]
end

#print Module
#print LinearMap

section
  variable {K V W : Type*} [Field K]
  variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

  example (f : V →ₗ[K] W) (a : K) (u v : V) :
      f (a • u + v) = a • f u + f v := by
    rw [map_add, map_smul]

  example (a b : K) (u v : V) :
      a • (u + v) + b • (u - v) = (a + b) • u + (a - b) • v := by
    module
end

section
  open Complex
  open scoped ComplexConjugate

  #synth Module ℝ ℂ
  #synth Module ℂ ℂ
  #check (conjAe.toLinearMap : ℂ →ₗ[ℝ] ℂ)

  example (r : ℝ) (z : ℂ) : conj (r • z) = r • conj z :=
    conjAe.toLinearMap.map_smul r z

  example : ¬ ∃ f : ℂ →ₗ[ℂ] ℂ, ∀ z, f z = conj z := by
    rintro ⟨f, hf⟩
    have h : -I = I := by
      simpa [hf, smul_eq_mul] using f.map_smul I (1 : ℂ)
    have him := congrArg im h
    norm_num at him

  #check ((starLinearEquiv ℂ).toLinearMap : ℂ →ₛₗ[conj] ℂ)
  example (a z : ℂ) : conj (a • z) = conj a • conj z := map_mul conj a z
end

/- Agreement on generators -/

section
  variable {R V W : Type*} [Semiring R]
  variable [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
  variable {s : Set V} {f g : V →ₗ[R] W}

  #print Submodule.span
  #synth CompleteLattice (Submodule R V)

  example (p : Submodule R V) : Submodule.span R s ≤ p ↔ s ⊆ p :=
    Submodule.span_le

  example {u v : V} (hu : u ∈ s) (hv : v ∈ s) (a : R) :
      a • u + v ∈ Submodule.span R s := by
    apply Submodule.add_mem
    · exact Submodule.smul_mem _ a (Submodule.subset_span hu)
    · exact Submodule.subset_span hv

  #check (f.eqLocus g : Submodule R V)
  example (x : V) : x ∈ f.eqLocus g ↔ f x = g x := Iff.rfl

  theorem agree_on_span (h : Set.EqOn f g s) :
      Set.EqOn f g (Submodule.span R s) := by
    change Submodule.span R s ≤ f.eqLocus g
    exact Submodule.span_le.mpr h

  example (hs : Submodule.span R s = ⊤) (h : Set.EqOn f g s) : f = g := by
    ext x
    have hx : x ∈ Submodule.span R s := by simp [hs]
    exact agree_on_span h hx

  #check LinearMap.ext_on
end

/- Finite linear combinations -/

#print Finsupp
#check (Finsupp.single 3 (2 : ℚ) : ℕ →₀ ℚ)

lemma finsupp_ne_const_one (c : ℕ →₀ ℚ) : (c : ℕ → ℚ) ≠ fun _ ↦ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset c.support
  have hz : c n = 0 := Finsupp.notMem_support_iff.mp hn
  exact zero_ne_one (hz.symm.trans (congrFun h n))

section
  variable {ι R V : Type*} [Semiring R] [AddCommMonoid V] [Module R V]
  variable (v : ι → V)

  #check (Finsupp.linearCombination R v : (ι →₀ R) →ₗ[R] V)

  example (c : ι →₀ R) :
      Finsupp.linearCombination R v c = ∑ i ∈ c.support, c i • v i := rfl

  example (i : ι) (a : R) :
      Finsupp.linearCombination R v (Finsupp.single i a) = a • v i := by simp

  example : LinearMap.range (Finsupp.linearCombination R v) = Submodule.span R (Set.range v) :=
    Finsupp.range_linearCombination R
end

def unitSeq (n : ℕ) : ℕ → ℚ := Pi.single n 1

example (n k : ℕ) : unitSeq n k = if k = n then 1 else 0 := by
  simp [unitSeq, Pi.single_apply]

example : (fun _ : ℕ ↦ (1 : ℚ)) ∉ Submodule.span ℚ (Set.range unitSeq) := by
  intro h
  let incl : (ℕ →₀ ℚ) →ₗ[ℚ] (ℕ → ℚ) := Finsupp.lcoeFun
  have hspan : Submodule.span ℚ (Set.range unitSeq) ≤ incl.range := by
    apply Submodule.span_le.mpr
    rintro _ ⟨n, rfl⟩
    exact ⟨Finsupp.single n 1, Finsupp.single_eq_pi_single n 1⟩
  obtain ⟨c, hc⟩ := hspan h
  exact finsupp_ne_const_one c hc

/- A basis gives coordinates -/

#print Module.Basis

section
  variable {ι K V W : Type*} [Field K]
  variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  variable (b : Module.Basis ι K V)

  #check (b.repr : V ≃ₗ[K] (ι →₀ K))
  #check (b : ι → V)
  example (i : ι) : b i = b.repr.symm (Finsupp.single i 1) := rfl

  example (i : ι) : b.repr (b i) = Finsupp.single i 1 := b.repr_self i
  example (x : V) : Finsupp.linearCombination K b (b.repr x) = x :=
    b.linearCombination_repr x

  example [Fintype ι] (x : V) : ∑ i, b.repr x i • b i = x := b.sum_repr x

  #check b.linearIndependent
  #check b.span_eq
  #check Module.Basis.mk

  /- Extending a map from a basis -/

  #check (b.constr K : (ι → W) ≃ₗ[K] (V →ₗ[K] W))

  example (w : ι → W) (x : V) :
      b.constr K w x = (b.repr x).sum (fun i a ↦ a • w i) := b.constr_apply K w x

  example (f : V →ₗ[K] W) (i : ι) : (b.constr K).symm f i = f (b i) := rfl

  example (w : ι → W) : ∃! f : V →ₗ[K] W, ∀ i, f (b i) = w i := by
    refine ⟨b.constr K w, b.constr_basis K w, ?_⟩
    intro f hf
    apply b.ext
    intro i
    rw [hf, b.constr_basis]
end

section
  open Complex

  #check (basisOneI : Module.Basis (Fin 2) ℝ ℂ)
  example (z : ℂ) : (basisOneI.repr z : Fin 2 → ℝ) = ![z.re, z.im] := coe_basisOneI_repr z

  example (f : ℂ →ₗ[ℝ] ℂ) (h₁ : f 1 = 1) (hI : f I = -I) :
      f = conjAe.toLinearMap := by
    apply basisOneI.ext
    intro i
    fin_cases i <;> simp [h₁, hI]
end

/- Matrices -/

#print Matrix

example {m n k R : Type*} [Fintype n] [AddCommMonoid R] [Mul R]
    (A : Matrix m n R) (B : Matrix n k R) (i : m) (j : k) :
    (A * B) i j = ∑ t, A i t * B t j := Matrix.mul_apply

section
  open Complex

  #check (LinearMap.toMatrix basisOneI basisOneI :
    (ℂ →ₗ[ℝ] ℂ) ≃ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ)

  example (f : ℂ →ₗ[ℝ] ℂ) (i j : Fin 2) :
      f.toMatrix basisOneI basisOneI i j = basisOneI.repr (f (basisOneI j)) i :=
    LinearMap.toMatrix_apply _ _ f i j

  example : conjAe.toLinearMap.toMatrix basisOneI basisOneI = !![1, 0; 0, -1] :=
    toMatrix_conjAe

  example (f g : ℂ →ₗ[ℝ] ℂ) :
      (f.comp g).toMatrix basisOneI basisOneI =
        f.toMatrix basisOneI basisOneI * g.toMatrix basisOneI basisOneI :=
    LinearMap.toMatrix_comp _ _ _ f g

  #check (Algebra.leftMulMatrix basisOneI : ℂ →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℝ)

  example (z : ℂ) : Algebra.leftMulMatrix basisOneI z =
      (Algebra.lmul ℝ ℂ z).toMatrix basisOneI basisOneI := rfl

  lemma complex_mul_matrix (z : ℂ) :
      Algebra.leftMulMatrix basisOneI z = !![z.re, -z.im; z.im, z.re] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Algebra.leftMulMatrix_eq_repr_mul]

  example (z : ℂ) : normSq z = z.re ^ 2 + z.im ^ 2 := by
    rw [normSq_apply, sq, sq]

  lemma det_complex_mul_matrix (z : ℂ) : (Algebra.leftMulMatrix basisOneI z).det = normSq z := by
    rw [complex_mul_matrix, Matrix.det_fin_two, normSq_apply]
    simp

  example (z w : ℂ) : normSq (z * w) = normSq z * normSq w := by
    rw [← det_complex_mul_matrix (z * w), map_mul, Matrix.det_mul]
    rw [det_complex_mul_matrix, det_complex_mul_matrix]
end

/-!
# Exercises
-/

section hw
  open Complex
  open scoped ComplexConjugate

  noncomputable def planeMap (a b : ℂ) : ℂ →ₗ[ℝ] ℂ :=
    a • LinearMap.id + b • conjAe.toLinearMap

  theorem existsUnique_planeMap (f : ℂ →ₗ[ℝ] ℂ) :
      ∃! p : ℂ × ℂ, f = planeMap p.1 p.2 := by
    sorry

  theorem det_planeMap (a b : ℂ) : (planeMap a b).det = normSq a - normSq b := by
    sorry

  theorem bijective_planeMap_iff (a b : ℂ) :
      Function.Bijective (planeMap a b) ↔ ‖a‖ ≠ ‖b‖ := by
    sorry
end hw

end Seminar10

#check Eq.rec
