import GNC.Estimation.CovariancePropagation

/-! Moment certificates from a uniform prediction error. These results
apply to arbitrary supported probability laws, retain cross-covariances,
and do not assume that the prediction residual is independent of the
prediction. Affine features may encode initial conditions, nonlinear
parameter features, or finitely many correlated input coefficients.
This is not an Ito/white-noise propagation theorem. -/
noncomputable section
open Matrix MeasureTheory ProbabilityTheory
namespace GNC.Estimation.PredictionMoments
open CovariancePropagation
variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

private theorem covariance_zero_of_variance_zero {X Y : Ω → ℝ}
    (hX : MemLp X 2 μ) (h : variance X μ=0) : covariance X Y μ=0 := by
  unfold covariance
  apply integral_eq_zero_of_ae
  filter_upwards [ae_eq_integral_of_variance_eq_zero hX h] with ω hω
  simp [hω]

/-- Cauchy--Schwarz in supplied standard-deviation bounds, including zero
variance. Derivation uses mathlib's variance identities. -/
theorem covariance_bound {X Y : Ω → ℝ} {a b : ℝ}
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (ha : 0≤a) (hb : 0≤b)
    (hvX : variance X μ≤a^2) (hvY : variance Y μ≤b^2) :
    |covariance X Y μ|≤a*b := by
  rcases eq_or_lt_of_le ha with ha0 | ha
  · have hz : variance X μ=0 := by nlinarith [variance_nonneg X μ]
    rw [covariance_zero_of_variance_zero μ hX hz]
    simpa only [abs_zero] using mul_nonneg ha hb
  rcases eq_or_lt_of_le hb with hb0 | hb
  · have hz : variance Y μ=0 := by nlinarith [variance_nonneg Y μ]
    rw [covariance_comm, covariance_zero_of_variance_zero μ hY hz]
    simpa only [abs_zero] using mul_nonneg ha.le hb
  have hm := variance_nonneg (fun ω => b*X ω-a*Y ω) μ
  have hp := variance_nonneg (fun ω => b*X ω+a*Y ω) μ
  rw [variance_fun_sub (hX.const_mul b) (hY.const_mul a)] at hm
  rw [variance_fun_add (hX.const_mul b) (hY.const_mul a)] at hp
  simp only [variance_const_mul,covariance_const_mul_left,covariance_const_mul_right] at hm hp
  have hxb := mul_le_mul_of_nonneg_left hvX (sq_nonneg b)
  have hyb := mul_le_mul_of_nonneg_left hvY (sq_nonneg a)
  apply abs_le.mpr
  constructor
  · refine le_of_mul_le_mul_left ?_ (show 0<2*a*b by positivity)
    nlinarith
  · refine le_of_mul_le_mul_left ?_ (show 0<2*a*b by positivity)
    nlinarith

theorem mean_error_bound {X Y : Ω → ℝ} {ε : ℝ}
    (hX : Integrable X μ) (hY : Integrable Y μ)
    (h : ∀ᵐ ω ∂μ, |X ω-Y ω|≤ε) :
    |(∫ ω, X ω ∂μ)-(∫ ω, Y ω ∂μ)|≤ε := by
  rw [← integral_sub hX hY]
  have hn : ∀ᵐ ω ∂μ, ‖X ω-Y ω‖≤ε := by simpa only [Real.norm_eq_abs] using h
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const hn

/-- Every entry of the full covariance matrix has an explicit error bound.
The two residuals can depend arbitrarily on one another and on the predictor. -/
theorem covariance_error_bound {X₁ X₂ Y₁ Y₂ : Ω → ℝ} {ε₁ ε₂ σ₁ σ₂ : ℝ}
    (hX₁ : MemLp X₁ 2 μ) (hX₂ : MemLp X₂ 2 μ)
    (hY₁ : MemLp Y₁ 2 μ) (hY₂ : MemLp Y₂ 2 μ)
    (hε₁ : 0≤ε₁) (hε₂ : 0≤ε₂) (hσ₁ : 0≤σ₁) (hσ₂ : 0≤σ₂)
    (he₁ : ∀ᵐ ω ∂μ, |X₁ ω-Y₁ ω|≤ε₁)
    (he₂ : ∀ᵐ ω ∂μ, |X₂ ω-Y₂ ω|≤ε₂)
    (hv₁ : variance Y₁ μ≤σ₁^2) (hv₂ : variance Y₂ μ≤σ₂^2) :
    |covariance X₁ X₂ μ-covariance Y₁ Y₂ μ|≤σ₁*ε₂+σ₂*ε₁+ε₁*ε₂ := by
  let e₁ := fun ω => X₁ ω-Y₁ ω
  let e₂ := fun ω => X₂ ω-Y₂ ω
  have hm₁ : MemLp e₁ 2 μ := hX₁.sub hY₁
  have hm₂ : MemLp e₂ 2 μ := hX₂.sub hY₂
  have hvE₁ := residual_variance_bound μ hX₁.aemeasurable hY₁.aemeasurable he₁
  have hvE₂ := residual_variance_bound μ hX₂.aemeasurable hY₂.aemeasurable he₂
  have hc₁ := covariance_bound μ hY₁ hm₂ hσ₁ hε₂ hv₁ hvE₂
  have hc₂ := covariance_bound μ hm₁ hY₂ hε₁ hσ₂ hvE₁ hv₂
  have hc₃ := covariance_bound μ hm₁ hm₂ hε₁ hε₂ hvE₁ hvE₂
  have hid₁ : X₁=Y₁+e₁ := by funext ω; dsimp [e₁]; ring
  have hid₂ : X₂=Y₂+e₂ := by funext ω; dsimp [e₂]; ring
  have hcov : covariance X₁ X₂ μ-covariance Y₁ Y₂ μ=
      covariance Y₁ e₂ μ+covariance e₁ Y₂ μ+covariance e₁ e₂ μ := by
    conv_lhs => rw [hid₁,hid₂,covariance_add_left hY₁ hm₁ (hY₂.add hm₂),
      covariance_add_right hY₁ hY₂ hm₂,covariance_add_right hm₁ hY₂ hm₂]
    ring
  rw [hcov]
  calc
    _ ≤ |covariance Y₁ e₂ μ|+|covariance e₁ Y₂ μ|+|covariance e₁ e₂ μ| :=
      by linarith [abs_add_le (covariance Y₁ e₂ μ+covariance e₁ Y₂ μ) (covariance e₁ e₂ μ),
        abs_add_le (covariance Y₁ e₂ μ) (covariance e₁ Y₂ μ)]
    _ ≤ _ := by nlinarith

variable {m n : Type*} [Fintype m] [Fintype n]

omit [Fintype m] in
theorem affine_memLp (c : m → ℝ) (H : Matrix m n ℝ) (Z : Ω → n → ℝ)
    (hZ : ∀ j, MemLp (fun ω => Z ω j) 2 μ) (i : m) :
    MemLp (fun ω => c i+(H *ᵥ Z ω) i) 2 μ := by
  apply (memLp_const (c i)).add
  simpa only [Matrix.mulVec,dotProduct,Finset.sum_fn] using
    memLp_finset_sum' Finset.univ (fun j _ => (hZ j).const_mul (H i j))

omit [Fintype m] in
theorem affine_mean (c : m → ℝ) (H : Matrix m n ℝ) (Z : Ω → n → ℝ)
    (hZ : ∀ j, MemLp (fun ω => Z ω j) 2 μ) (i : m) :
    (∫ ω, c i+(H *ᵥ Z ω) i ∂μ)=c i+(H *ᵥ (fun j => ∫ ω, Z ω j ∂μ)) i := by
  have hL : Integrable (fun ω => (H *ᵥ Z ω) i) μ := by
    have hm : MemLp (fun ω => (H *ᵥ Z ω) i) 2 μ := by
      simpa only [Matrix.mulVec,dotProduct,Finset.sum_fn] using
        memLp_finset_sum' Finset.univ (fun j _ => (hZ j).const_mul (H i j))
    exact hm.integrable (by norm_num)
  rw [integral_add (integrable_const _) hL]
  simp only [integral_const,probReal_univ,one_smul,Matrix.mulVec,dotProduct]
  rw [integral_finset_sum _ (fun j _ => ((hZ j).integrable (by norm_num)).const_mul (H i j))]
  simp only [integral_const_mul]

/-- Exact covariance of an affine feature response. A joint feature vector
retains initial/input and temporal input correlations without independence. -/
theorem affine_pushforward (c : m → ℝ) (H : Matrix m n ℝ) (Z : Ω → n → ℝ)
    (hZ : ∀ j, MemLp (fun ω => Z ω j) 2 μ) :
    covarianceMatrix μ (fun ω i => c i+(H *ᵥ Z ω) i)=H*covarianceMatrix μ Z*Hᵀ := by
  have hL (i : m) : MemLp (fun ω => (H *ᵥ Z ω) i) 2 μ := by
    simpa only [Matrix.mulVec,dotProduct,Finset.sum_fn] using
      memLp_finset_sum' Finset.univ (fun j _ => (hZ j).const_mul (H i j))
  rw [← linear_pushforward μ H Z hZ]
  ext i j
  exact (covariance_const_add_left ((hL i).integrable (by norm_num)) (c i)).trans
    (covariance_const_add_right ((hL j).integrable (by norm_num)) (c j))

omit [Fintype m] in
/-- Prediction, mean and full covariance guarantee at any selected time.
For an all-time tube this theorem is applied at each time, with the same
supported probability law. Moment bounds on the predictor are premises,
not replaced by sampled or floating-point estimates. -/
theorem prediction_and_moments (X Y : Ω → m → ℝ) (ε σ : m → ℝ)
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ)
    (hY : ∀ i, MemLp (fun ω => Y ω i) 2 μ)
    (hε : ∀ i, 0≤ε i) (hσ : ∀ i, 0≤σ i)
    (he : ∀ i, ∀ᵐ ω ∂μ, |X ω i-Y ω i|≤ε i)
    (hv : ∀ i, variance (fun ω => Y ω i) μ≤σ i^2) :
    (∀ i, |(∫ ω, X ω i ∂μ)-(∫ ω, Y ω i ∂μ)|≤ε i) ∧
    (∀ i j, |covarianceMatrix μ X i j-covarianceMatrix μ Y i j|≤
      σ i*ε j+σ j*ε i+ε i*ε j) := by
  constructor
  · intro i
    exact mean_error_bound μ ((hX i).integrable (by norm_num))
      ((hY i).integrable (by norm_num)) (he i)
  · intro i j
    exact covariance_error_bound μ (hX i) (hX j) (hY i) (hY j)
      (hε i) (hε j) (hσ i) (hσ j) (he i) (he j) (hv i) (hv j)

/-- Full propagation and error theorem for a finite response representation.
Time-dependent matrices can represent the STM and responses to uncertain
input coefficients; nonlinear parameter features are also allowed. -/
theorem affine_prediction_certificate (X : Ω → m → ℝ) (c : m → ℝ)
    (H : Matrix m n ℝ) (Z : Ω → n → ℝ) (ε σ : m → ℝ)
    (hX : ∀ i, MemLp (fun ω => X ω i) 2 μ)
    (hZ : ∀ j, MemLp (fun ω => Z ω j) 2 μ)
    (hε : ∀ i, 0≤ε i) (hσ : ∀ i, 0≤σ i)
    (he : ∀ i, ∀ᵐ ω ∂μ, |X ω i-(c i+(H *ᵥ Z ω) i)|≤ε i)
    (hv : ∀ i, (H*covarianceMatrix μ Z*Hᵀ) i i≤σ i^2) :
    covarianceMatrix μ (fun ω i => c i+(H *ᵥ Z ω) i)=H*covarianceMatrix μ Z*Hᵀ ∧
    (∀ i, |(∫ ω, X ω i ∂μ)-(∫ ω, c i+(H *ᵥ Z ω) i ∂μ)|≤ε i) ∧
    (∀ i j, |covarianceMatrix μ X i j-(H*covarianceMatrix μ Z*Hᵀ) i j|≤
      σ i*ε j+σ j*ε i+ε i*ε j) := by
  have hP := affine_pushforward μ c H Z hZ
  have hY := affine_memLp μ c H Z hZ
  have hvY (i : m) : variance (fun ω => c i+(H *ᵥ Z ω) i) μ≤σ i^2 := by
    rw [← covariance_self (hY i).aemeasurable]
    change covarianceMatrix μ (fun ω i => c i+(H *ᵥ Z ω) i) i i≤_
    rw [hP]
    exact hv i
  have h := prediction_and_moments μ X (fun ω i => c i+(H *ᵥ Z ω) i)
    ε σ hX hY hε hσ he hvY
  exact ⟨hP,h.1,by simpa only [hP] using h.2⟩

end GNC.Estimation.PredictionMoments
