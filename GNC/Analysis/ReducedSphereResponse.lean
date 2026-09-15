import GNC.Analysis.SphereRankOne

/-! A five-feature response can be integrated directly, without constructing
the full quadratic tensor first. Its omitted Hessian terms are explicit.
The coefficient dynamics may vary with time. These identities do not supply
a physical trajectory certificate or an end-to-end solver cost comparison. -/
noncomputable section
namespace GNC.ReducedSphereResponse

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def value (u v c : ℝ) (U V D Q W : E) : E :=
  u • U + v • V + c • D + u^2 • Q + (u*v) • W

def first (u v c : ℝ) (U V C : E) : E := u • U + v • V + c • C

/-- This is the same geometric reduction applied before, rather than after,
constructing the complete response. The mixed transverse term is retained. -/
theorem response_decomposition (u v c : ℝ) (hs : u^2+v^2=2*c-c^2)
    (U V C Uu Uv Vv Cu Cv Cc : E) :
    SphereResponse.quadratic u v c U V C Uu Uv Vv Cu Cv Cc =
      value u v c U V (C+2 • Vv) (Uu-Vv) Uv +
        (c*u) • Cu + (c*v) • Cv + c^2 • (Cc-Vv) := by
  rw [SphereRankOne.decomposition u v c hs]
  unfold SphereRankOne.compressed value
  module

/-- The retained quadratic source uses only the two transverse first
responses. The coefficient of the axial deficit carries both curvatures. -/
def retained (H : E →ₗ[ℝ] E →ₗ[ℝ] E) (u v c : ℝ) (U V : E) : E :=
  u^2 • H U U + (2*c-u^2) • H V V + (u*v) • (H U V + H V U)

def omitted (H : E →ₗ[ℝ] E →ₗ[ℝ] E) (u v c : ℝ) (U V C : E) : E :=
  c^2 • (H C C-H V V) + (c*u) • (H C U+H U C) +
    (c*v) • (H C V+H V C)

/-- No symmetry assumption on the bilinear map is needed. -/
theorem source_decomposition (H : E →ₗ[ℝ] E →ₗ[ℝ] E)
    (u v c : ℝ) (hs : u^2+v^2=2*c-c^2) (U V C : E) :
    H (first u v c U V C) (first u v c U V C) =
      retained H u v c U V + omitted H u v c U V C := by
  have hv : v^2=2*c-c^2-u^2 := by linarith
  calc
    _ = u^2 • H U U + (u*v) • (H U V+H V U) + v^2 • H V V +
        (c*u) • (H C U+H U C) + (c*v) • (H C V+H V C) + c^2 • H C C := by
      unfold first
      simp only [map_add,map_smul,LinearMap.add_apply,LinearMap.smul_apply]
      module
    _ = _ := by
      rw [hv]
      unfold retained omitted
      module

section Dynamics
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Five coefficient curves suffice for the retained response. In particular,
there is no separate axial first-response curve or full second-order tensor
among the hypotheses. `A`, `H`, and all three sources can vary with time. -/
theorem derivative
    (A : ℝ → F →ₗ[ℝ] F) (H : ℝ → F →ₗ[ℝ] F →ₗ[ℝ] F)
    (U V D Q W fU fV fC : ℝ → F) (u v c t : ℝ)
    (hU : HasDerivAt U (A t (U t)+fU t) t)
    (hV : HasDerivAt V (A t (V t)+fV t) t)
    (hD : HasDerivAt D (A t (D t)+fC t+2 • H t (V t) (V t)) t)
    (hQ : HasDerivAt Q (A t (Q t)+H t (U t) (U t)-H t (V t) (V t)) t)
    (hW : HasDerivAt W (A t (W t)+H t (U t) (V t)+H t (V t) (U t)) t) :
    HasDerivAt (fun s => value u v c (U s) (V s) (D s) (Q s) (W s))
      (A t (value u v c (U t) (V t) (D t) (Q t) (W t)) +
        first u v c (fU t) (fV t) (fC t) + retained (H t) u v c (U t) (V t)) t := by
  convert ((((hU.const_smul u).add (hV.const_smul v)).add
    (hD.const_smul c)).add (hQ.const_smul (u^2))).add
    (hW.const_smul (u*v)) using 1
  unfold value first retained
  simp only [map_add,map_smul]
  module

/-- Equivalently, the direct response has the full quadratic source minus
the stated omitted terms. `C` is used only to express that comparison. -/
theorem derivative_with_defect
    (A : ℝ → F →ₗ[ℝ] F) (H : ℝ → F →ₗ[ℝ] F →ₗ[ℝ] F)
    (U V C D Q W fU fV fC : ℝ → F) (u v c t : ℝ)
    (hs : u^2+v^2=2*c-c^2)
    (hU : HasDerivAt U (A t (U t)+fU t) t)
    (hV : HasDerivAt V (A t (V t)+fV t) t)
    (hD : HasDerivAt D (A t (D t)+fC t+2 • H t (V t) (V t)) t)
    (hQ : HasDerivAt Q (A t (Q t)+H t (U t) (U t)-H t (V t) (V t)) t)
    (hW : HasDerivAt W (A t (W t)+H t (U t) (V t)+H t (V t) (U t)) t) :
    HasDerivAt (fun s => value u v c (U s) (V s) (D s) (Q s) (W s))
      (A t (value u v c (U t) (V t) (D t) (Q t) (W t)) +
        first u v c (fU t) (fV t) (fC t) +
        H t (first u v c (U t) (V t) (C t)) (first u v c (U t) (V t) (C t)) -
        omitted (H t) u v c (U t) (V t) (C t)) t := by
  rw [source_decomposition (H t) u v c hs]
  simpa only [← add_assoc,add_sub_cancel_right] using
    derivative A H U V D Q W fU fV fC u v c t hU hV hD hQ hW

theorem initial (U V D Q W : ℝ → F) (u v c : ℝ)
    (hU : U 0=0) (hV : V 0=0) (hD : D 0=0) (hQ : Q 0=0) (hW : W 0=0) :
    value u v c (U 0) (V 0) (D 0) (Q 0) (W 0)=0 := by
  simp [value,hU,hV,hD,hQ,hW]

/-- A cap-depth bound yields a cubic/quartic source bound, rather than
discarding a leading quadratic pointing term. The response norms remain
time dependent; no smallness is asserted without bounding them. -/
theorem omitted_bound (H : F →ₗ[ℝ] F →ₗ[ℝ] F)
    {u v c σ δ : ℝ} (hδ : 0≤δ)
    (hu : |u|≤σ) (hv : |v|≤σ) (hc : |c|≤δ) (U V C : F) :
    ‖omitted H u v c U V C‖ ≤
      δ^2 * ‖H C C-H V V‖ +
        δ*σ * (‖H C U+H U C‖+‖H C V+H V C‖) := by
  have hcc : |c^2|≤δ^2 := by
    rw [abs_pow]
    nlinarith [abs_nonneg c]
  have hcu : |c*u|≤δ*σ := by
    rw [abs_mul]
    exact mul_le_mul hc hu (abs_nonneg u) hδ
  have hcv : |c*v|≤δ*σ := by
    rw [abs_mul]
    exact mul_le_mul hc hv (abs_nonneg v) hδ
  calc
    _ ≤ ‖c^2 • (H C C-H V V)‖ + ‖(c*u) • (H C U+H U C)‖ +
        ‖(c*v) • (H C V+H V C)‖ := norm_add₃_le
    _ = |c^2| * ‖H C C-H V V‖ + |c*u| * ‖H C U+H U C‖ +
        |c*v| * ‖H C V+H V C‖ := by simp only [norm_smul,Real.norm_eq_abs]
    _ ≤ δ^2 * ‖H C C-H V V‖ + δ*σ * ‖H C U+H U C‖ +
        δ*σ * ‖H C V+H V C‖ := by gcongr
    _ = _ := by ring

theorem cap_omitted_bound (H : F →ₗ[ℝ] F →ₗ[ℝ] F)
    {u v c σ : ℝ} (hσ : 0≤σ) (hσ1 : σ<1) (hc0 : 0≤c) (hc1 : c≤1)
    (hs : u^2+v^2=2*c-c^2) (hcap : u^2+v^2≤σ^2) (U V C : F) :
    let δ := σ^2/(2-σ^2)
    ‖omitted H u v c U V C‖ ≤ δ^2 * ‖H C C-H V V‖ +
      δ*σ * (‖H C U+H U C‖+‖H C V+H V C‖) := by
  have hsq : σ^2<1 := by nlinarith
  have hδ : 0≤σ^2/(2-σ^2) := div_nonneg (sq_nonneg _) (by linarith)
  have hu : |u|≤σ := (sq_le_sq₀ (abs_nonneg u) hσ).1 (by
    rw [sq_abs]
    nlinarith [sq_nonneg v])
  have hv : |v|≤σ := (sq_le_sq₀ (abs_nonneg v) hσ).1 (by
    rw [sq_abs]
    nlinarith [sq_nonneg u])
  have hc : |c|≤σ^2/(2-σ^2) := by
    rw [abs_of_nonneg hc0]
    exact SphereResponse.cap_depth_bound hc0 hc1 hsq hs hcap
  exact omitted_bound H hδ hu hv hc U V C

/-- A simpler order statement: the omitted forcing is cubic/quartic in
cap radius. No acceleration, gravity or time-integration residual is covered
by this source bound alone. -/
theorem cubic_omitted_bound (H : F →ₗ[ℝ] F →ₗ[ℝ] F)
    {u v c σ : ℝ} (hσ : 0≤σ) (hσ1 : σ<1) (hc0 : 0≤c) (hc1 : c≤1)
    (hs : u^2+v^2=2*c-c^2) (hcap : u^2+v^2≤σ^2) (U V C : F) :
    ‖omitted H u v c U V C‖ ≤ σ^4 * ‖H C C-H V V‖ +
      σ^3 * (‖H C U+H U C‖+‖H C V+H V C‖) := by
  have hsq : σ^2<1 := by nlinarith
  have hd : 0≤σ^2/(2-σ^2) := div_nonneg (sq_nonneg _) (by linarith)
  have hds : σ^2/(2-σ^2)≤σ^2 := by
    apply (div_le_iff₀ (by linarith : 0<2-σ^2)).2
    nlinarith [mul_nonneg (sq_nonneg σ) (show 0≤1-σ^2 by linarith)]
  have h := cap_omitted_bound H hσ hσ1 hc0 hc1 hs hcap U V C
  dsimp only at h
  calc
    _ ≤ _ := h
    _ ≤ (σ^2)^2 * ‖H C C-H V V‖ +
        σ^2*σ * (‖H C U+H U C‖+‖H C V+H V C‖) := by gcongr
    _ = _ := by ring

end Dynamics

open Planning.FlopKernel
variable {K : Type*} [CommSemiring K]

/-- A normal output retaining the mixed transverse response. Inputs and
time coefficients are prepared; construction and loads are separate. -/
def queryNormal (u v V W : K) : Value K :=
  mul (input v) (add (input V) (mul (input u) (input W)))

theorem queryNormal_value (u v V W : K) :
    (queryNormal u v V W).value = v*V+(u*v)*W := by
  simp only [queryNormal,Planning.FlopKernel.add,Planning.FlopKernel.mul,input]
  ring

theorem queryNormal_flops (u v V W : K) : (queryNormal u v V W).flops=3 := rfl

/-- The spatially factored five-feature algorithm costs thirteen scalar
adds/multiplies. Applying it to a physical candidate also requires proving
that candidate's factorization and complete trajectory bound. -/
theorem spatial_query_flops (u v c L0 C0 Q0 L1 C1 Q1 V W : K) :
    (SphereRankOne.queryComponent u c L0 C0 Q0).flops +
      (SphereRankOne.queryComponent u c L1 C1 Q1).flops +
      (queryNormal u v V W).flops = 13 := rfl

end GNC.ReducedSphereResponse
