import GNC.Dynamics.GravityField
import GNC.Analysis.FundamentalSolution
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Operator.Prod

/-! Continuous variational responses along any nonsingular reference.
Existence reuses the library's forced linear ODE theorem. The reference
and forcing may vary arbitrarily in time; no frozen-gravity approximation
or angular Taylor expansion is imposed. -/
noncomputable section
open Set
open scoped RealInnerProductSpace
namespace GNC.GravityLinearResponse
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def gradientMap (μ : ℝ) (q : E) : E →L[ℝ] E :=
  (3*μ/‖q‖^5) • (innerSL ℝ q).smulRight q-
    (μ/‖q‖^3) • ContinuousLinearMap.id ℝ E

theorem gradientMap_apply (μ : ℝ) (q v : E) :
    gradientMap μ q v=Gravity.gradient μ q v := by
  simp only [gradientMap,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply,innerSL_apply_apply,Gravity.gradient]
  module

structure Response (μ scale : ℝ) (q f : ℝ → E) where
  p : ℝ → E
  v : ℝ → E
  continuous_p : Continuous p
  continuous_v : Continuous v
  initial_p : p 0=0
  initial_v : v 0=0
  derivative_p : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt p (v t) t
  derivative_v : ∀ t ∈ Icc (0:ℝ) 1,
    HasDerivAt v (scale • (Gravity.gradient μ (q t) (p t)+f t)) t

theorem Response.exists (μ scale : ℝ) {q f : ℝ → E} (hq : Continuous q)
    (hq0 : ∀ t, q t≠0) (hf : Continuous f) : Nonempty (Response μ scale q f) := by
  let A : ℝ → (E×E) →L[ℝ] (E×E) := fun t =>
    (ContinuousLinearMap.snd ℝ E E).prod
      (scale • ((gradientMap μ (q t)).comp (ContinuousLinearMap.fst ℝ E E)))
  have hG : Continuous (fun t => gradientMap μ (q t)) := by
    unfold gradientMap
    fun_prop (disch := intro t; exact pow_ne_zero _ (norm_ne_zero_iff.mpr (hq0 t)))
  have hA : Continuous A := by
    exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp
      (continuous_const.prodMk (show Continuous (fun t => scale •
        (gradientMap μ (q t)).comp (ContinuousLinearMap.fst ℝ E E)) by fun_prop))
  obtain ⟨x,hx,_⟩ := ForcedResponse.exists_unique_response A hA
    (fun t => ((0:E),scale • f t)) (by fun_prop) (0:E×E)
  have hd := hx.2
  have hc : Continuous x := continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt
  refine ⟨⟨fun t => (x t).1,fun t => (x t).2,hc.fst,hc.snd,
    by simp [hx.1],by simp [hx.1],?_,?_⟩⟩
  · intro t _
    simpa [A] using (ContinuousLinearMap.fst ℝ E E).hasFDerivAt.comp_hasDerivAt t (hd t)
  · intro t _
    simpa [A,gradientMap_apply,smul_add] using
      (ContinuousLinearMap.snd ℝ E E).hasFDerivAt.comp_hasDerivAt t (hd t)

/-- A finite family of response columns serves every constant parameter
vector. Angular nonlinearities may be retained in the weights themselves. -/
def Response.combine {ι : Type*} [Fintype ι] (μ scale : ℝ) (q : ℝ → E)
    (f : ι → ℝ → E) (S : ∀ i, Response μ scale q (f i)) (w : ι → ℝ) :
    Response μ scale q (fun t => ∑ i, w i • f i t) where
  p := fun t => ∑ i, w i • (S i).p t
  v := fun t => ∑ i, w i • (S i).v t
  continuous_p := continuous_finset_sum _ (fun i _ => (S i).continuous_p.const_smul _)
  continuous_v := continuous_finset_sum _ (fun i _ => (S i).continuous_v.const_smul _)
  initial_p := by simp [Response.initial_p]
  initial_v := by simp [Response.initial_v]
  derivative_p := fun t ht => HasDerivAt.fun_sum (fun i _ => ((S i).derivative_p t ht).const_smul _)
  derivative_v := fun t ht => by
    have h := HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => ((S i).derivative_v t ht).const_smul (w i))
    convert h using 1
    simp only [←gradientMap_apply, map_sum, map_smul, Finset.smul_sum,smul_add,
      smul_comm (w _) scale,Finset.sum_add_distrib]

end GNC.GravityLinearResponse
