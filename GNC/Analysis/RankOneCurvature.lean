import GNC.Analysis.PolynomialObstruction

/-! A rank-one quadratic cannot retain curvature in every input direction.
On its perpendicular line, linear and cubic terms are odd, and a signed
two-radius witness cancels every quartic term. This obstruction permits
arbitrary coefficients and different directions at each order. -/
namespace GNC.RankOneCurvature
open Finset
noncomputable section

def nodes (a b : ℝ) : Fin 4 → ℝ := ![b,-b,a,-a]
def weights (w : ℝ) : Fin 4 → ℝ := ![w/2,w/2,-(1-w)/2,-(1-w)/2]

theorem variation {w : ℝ} (h0 : 0≤w) (h1 : w≤1) :
    ∑ i, |weights w i|=1 := by
  simp [weights,Fin.sum_univ_four,abs_div,abs_of_nonneg h0,
    abs_of_nonpos (sub_nonpos.mpr h1)]
  linarith

theorem annihilates {a b w : ℝ} (h : w*b^4=(1-w)*a^4) (l c d : ℝ) :
    ∑ i, weights w i*(l*nodes a b i+c*(nodes a b i)^3+d*(nodes a b i)^4)=0 := by
  simp [weights,nodes,Fin.sum_univ_four]
  linear_combination d*h

/-- A scalar output of a degree-four rank-one directional expansion.
Factorial normalizations can be absorbed in `q`, `c`, and `d`. -/
def predictor (l0 l1 q w0 w1 c z0 z1 d h0 h1 u v : ℝ) : ℝ :=
  l0*u+l1*v+q*(w0*u+w1*v)^2+c*(z0*u+z1*v)^3+d*(h0*u+h1*v)^4

theorem perpendicular_slice (l0 l1 q w0 w1 c z0 z1 d h0 h1 t : ℝ) :
    predictor l0 l1 q w0 w1 c z0 z1 d h0 h1 (-w1*t) (w0*t)=
      (-l0*w1+l1*w0)*t+c*(-z0*w1+z1*w0)^3*t^3+
        d*(-h0*w1+h1*w0)^4*t^4 := by
  unfold predictor
  ring

/-- A unit-total-variation witness bounds the actual worst sample error.
The physical sample uncertainty is subtracted exactly once. -/
theorem physical_lower_bound {n : ℕ} [Nonempty (Fin n)]
    (w f a p : Fin n → ℝ) {ε γ : ℝ}
    (hw : ∑ i, |w i|=1) (hp : ∑ i, w i*p i=0)
    (hf : ∀ i, |f i-a i|≤ε) (ha : γ≤|∑ i, w i*a i|) :
    ∃ i, γ-ε≤|f i-p i| := by
  obtain ⟨i,_,hi⟩ := Finset.exists_max_image Finset.univ
    (fun i => |f i-p i|) (by simp)
  have he := PolynomialObstruction.sample_error w f p
    (fun _ => |f i-p i|) (fun j => hi j (by simp))
  rw [hp,sub_zero,←Finset.sum_mul,hw,one_mul] at he
  have hf' := PolynomialObstruction.sample_error w f a (fun _ => ε) hf
  rw [←Finset.sum_mul,hw,one_mul] at hf'
  have ht := abs_sub_le (∑ i, w i*a i) (∑ i, w i*f i) 0
  simp only [sub_zero] at ht
  rw [abs_sub_comm] at ht
  exact ⟨i,by linarith⟩

end
end GNC.RankOneCurvature
