import GNC.Applications.OrbitalComparison.TangentialReferenceData.Checked
import GNC.Analysis.PolynomialExtension
import GNC.Analysis.PositiveExtension
import GNC.Dynamics.PolynomialOrbitInvariant

/-! A changing Earth-orbit reference with constant-magnitude tangential thrust.
Reuses the exact polynomial gravity lift and released ODE existence theorem.
Numerical polynomials, their jumps and their differential defects are charged.
This reference certificate alone is not a certificate for a misaligned deputy.
-/
noncomputable section
namespace GNC.OrbitalComparison.TangentialReference
open PolynomialODE PolynomialOrbit TangentialReferenceData Set

def initial : Fin 5 → ℝ := ![1,0,0,1,1]
def sequence (j : ℕ) : Step 5 := if hj : j<32 then steps ⟨j,hj⟩ else step0

theorem sequence_valid (j : ℕ) (hj : j<32) : (sequence j).Valid (field alpha) := by
  simpa [sequence,hj] using valid ⟨j,hj⟩
theorem sequence_duration (j : ℕ) (hj : j<32) : (sequence j).duration=13/640 := by
  simpa [sequence,hj,stepLength] using durations ⟨j,hj⟩
theorem sequence_region (j : ℕ) (hj : j<32) : (sequence j).region≤(4/3:ℚ) := by
  simp [sequence,hj,regions]
theorem sequence_join (j : ℕ) (hj : j+1<32) : Compatible (sequence j) (sequence (j+1)) := by
  have hj' : j<32 := by omega
  simpa [sequence,hj,hj'] using joins ⟨j,by omega⟩
theorem sequence_error (j : ℕ) (hj : j<32) : (sequence j).error≤errorBound := by
  simpa [sequence,hj] using errors ⟨j,hj⟩

theorem initial_error : ‖initial-curve (sequence 0).coefficients 0‖≤
    ((sequence 0).initialError:ℝ) := by
  have he : curve (sequence 0).coefficients 0=initial := by
    ext i
    fin_cases i <;> norm_num [initial,sequence,steps,step0,curve,
      Planning.PolynomialKernel.evaluate,Matrix.cons_val_succ,Matrix.cons_val_zero]
  rw [he,sub_self,norm_zero]
  norm_num [sequence,steps,step0]

theorem slope_bound (i : Fin 5) : ((field alpha i).slope (4/3):ℝ)≤32 := by
  exact_mod_cast field_slope (a := alpha) (by norm_num [alpha]) i
theorem magnitude_bound (i : Fin 5) : ((field alpha i).majorant (4/3):ℝ)≤16 := by
  fin_cases i <;> norm_num [field,Expr.majorant,alpha]

theorem exists_lifted :
    ∃ z : ℝ → Fin 5 → ℝ, Continuous z ∧ z 0=initial ∧
      ∀ t ∈ Icc (0:ℝ) (13/20), HasDerivAt z (rate (alpha:ℝ) (z t)) t := by
  obtain ⟨z,hz,hi,hd⟩ := exists_solution_of_chain sequence (field alpha) 32
    (h := 13/640) (R := 4/3) (by norm_num) (by norm_num) (by norm_num)
    sequence_valid sequence_duration sequence_join sequence_region
    32 16 slope_bound magnitude_bound initial initial_error
  refine ⟨z,hz,hi,?_⟩
  intro t ht
  have h := hd t (by norm_num at ht ⊢; exact ht)
  simpa only [field_correct] using h

theorem exists_physical :
    ∃ w : ℝ → Fin 4 → ℝ, Continuous w ∧ (∀ t, 0<radius (w t)) ∧
      w 0=![1,0,0,1] ∧
      ∀ t ∈ Icc (0:ℝ) (13/20), HasDerivAt w (physicalRate (alpha:ℝ) (w t)) t := by
  obtain ⟨z,hz,hz0,hdz⟩ := exists_lifted
  have hc := constraint_preserved z hz hdz (by rw [hz0]; change ((1:ℝ)^2+0^2)*1^2-1=0; norm_num)
  have hu := inverse_pos_on z hz (by rw [hz0]; change (0:ℝ)<1; norm_num) hc
  let w := fun t => project (z t)
  have hw : Continuous w := by
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun t => z t 0)
      exact (continuous_apply 0).comp hz
    · change Continuous (fun t => z t 1)
      exact (continuous_apply 1).comp hz
    · change Continuous (fun t => z t 2)
      exact (continuous_apply 2).comp hz
    · change Continuous (fun t => z t 3)
      exact (continuous_apply 3).comp hz
  have hr (t : ℝ) (ht : t ∈ Icc (0:ℝ) (13/20)) : 0<radius (w t) :=
    radius_pos_of_constraint (hc t ht)
  have hdw (t : ℝ) (ht : t ∈ Icc (0:ℝ) (13/20)) :
      HasDerivAt w (physicalRate (alpha:ℝ) (w t)) t :=
    project_derivative (hdz t ht) (hc t ht) (hu t ht)
  have hrc : Continuous radius := by unfold radius; fun_prop
  obtain ⟨v,hv,hvp,hve⟩ := PositiveExtension.exists_positive w hw radius hrc (by norm_num) hr
  refine ⟨v,hv,hvp,?_,?_⟩
  · rw [(hve 0 (by constructor <;> norm_num)).self_of_nhds]
    simp [w,project,hz0,initial]
  · intro t ht
    rw [(hve t ht).self_of_nhds]
    exact (hdw t ht).congr_of_eventuallyEq (hve t ht)

theorem lifted_pieces (z : ℝ → Fin 5 → ℝ) (hz : Continuous z)
    (hd : ∀ t ∈ Icc (0:ℝ) (13/20), HasDerivAt z (rate (alpha:ℝ) (z t)) t)
    (hi : z 0=initial) :
    ∀ j : ℕ, j<32 → ∀ t ∈ Icc (0:ℝ) (13/640),
      ‖z ((j:ℝ)*(13/640)+t)-curve (sequence j).coefficients t‖<(errorBound:ℝ) := by
  have hc := chain_sound sequence (field alpha) 32 (by norm_num : (0:ℚ)≤13/640)
    sequence_valid sequence_duration sequence_join z hz (fun t ht => by
      have ht' : t ∈ Icc (0:ℝ) (13/20) := by norm_num at ht ⊢; exact ht
      convert hd t ht' using 1
      funext i
      exact field_correct alpha (z t) i) (by rw [hi]; exact initial_error)
  intro j hj t ht
  have herr : ((sequence j).error:ℝ)≤(errorBound:ℝ) := by
    exact_mod_cast sequence_error j hj
  have hb := (hc j hj t (by norm_num at ht ⊢; exact ht)).trans_le herr
  convert hb using 1 <;> norm_num

/-- Includes the numerical inverse-radius component, rather than assuming
the polynomial reference has exactly the physical radius. -/
theorem physical_pieces (w : ℝ → Fin 4 → ℝ) (hw : Continuous w)
    (hr : ∀ t, 0<radius (w t))
    (hd : ∀ t ∈ Icc (0:ℝ) (13/20), HasDerivAt w (physicalRate (alpha:ℝ) (w t)) t)
    (hi : w 0=![1,0,0,1]) :
    ∀ j : ℕ, j<32 → ∀ t ∈ Icc (0:ℝ) (13/640),
      ‖lift (w ((j:ℝ)*(13/640)+t))-curve (sequence j).coefficients t‖<(errorBound:ℝ) := by
  exact lifted_pieces (fun t => lift (w t)) (lift_continuous hw hr)
    (fun t ht => lift_derivative (hd t ht) (hr t)) (by
      change lift (w 0)=initial
      rw [hi]
      ext i
      fin_cases i <;> norm_num [lift,radius,initial,Matrix.cons_val_succ,Matrix.cons_val_zero] <;> rfl)

theorem physical_enclosure (w : ℝ → Fin 4 → ℝ) (hw : Continuous w)
    (hr : ∀ t, 0<radius (w t))
    (hd : ∀ t ∈ Icc (0:ℝ) (13/20), HasDerivAt w (physicalRate (alpha:ℝ) (w t)) t)
    (hi : w 0=![1,0,0,1]) :
    ∀ t ∈ Icc (0:ℝ) (13/20), ∃ j : ℕ, j<32 ∧ ∃ u ∈ Icc (0:ℝ) (13/640),
      t=(j:ℝ)*(13/640)+u ∧
        ‖lift (w t)-curve (sequence j).coefficients u‖<(errorBound:ℝ) := by
  intro t ht
  obtain ⟨j,hj,u,hu,he⟩ := grid_covers 32 (by norm_num : (0:ℝ)≤13/640) (by norm_num)
    (by norm_num at ht ⊢; exact ht)
  refine ⟨j,hj,u,hu,he,?_⟩
  rw [he]
  exact physical_pieces w hw hr hd hi j hj u hu

theorem endpoint_error (w : ℝ → Fin 4 → ℝ) (hw : Continuous w)
    (hr : ∀ t, 0<radius (w t))
    (hd : ∀ t ∈ Icc (0:ℝ) (13/20), HasDerivAt w (physicalRate (alpha:ℝ) (w t)) t)
    (hi : w 0=![1,0,0,1]) :
    ∀ i : Fin 2, |w (13/20) (i.castAdd 2)-(endpoint (i.castAdd 3):ℝ)|<(errorBound:ℝ) := by
  have h := physical_pieces w hw hr hd hi 31 (by norm_num) (13/640) (by constructor <;> norm_num)
  norm_num only [show (31:ℝ)*(13/640)+13/640=13/20 by norm_num] at h
  intro i
  have he := (norm_le_pi_norm (lift (w (13/20))-curve (sequence 31).coefficients (13/640))
    (i.castAdd 3 : Fin 5)).trans_lt h
  have hv : curve (sequence 31).coefficients (13/640) (i.castAdd 3 : Fin 5)=
      (endpoint (i.castAdd 3):ℝ) := by
    simpa [sequence,steps,endpoint,stepLength] using
      curve_rational step31.coefficients stepLength (i.castAdd 3 : Fin 5)
  rw [Pi.sub_apply,Real.norm_eq_abs,hv] at he
  fin_cases i <;> simpa only [lift,Matrix.cons_val_zero,Matrix.cons_val_one] using he

/-- The reference is genuinely noncircular: its endpoint radius is larger
than the initial radius, proved from the all-time numerical certificate. -/
theorem endpoint_radius (w : ℝ → Fin 4 → ℝ) (hw : Continuous w)
    (hr : ∀ t, 0<radius (w t))
    (hd : ∀ t ∈ Icc (0:ℝ) (13/20), HasDerivAt w (physicalRate (alpha:ℝ) (w t)) t)
    (hi : w 0=![1,0,0,1]) :
    (radialLower:ℝ)<radius (w (13/20)) ∧ radius (w (13/20))<(radialUpper:ℝ) := by
  have h0 := abs_lt.mp (endpoint_error w hw hr hd hi 0)
  have h1 := abs_lt.mp (endpoint_error w hw hr hd hi 1)
  change -(errorBound:ℝ)<w (13/20) 0-(endpoint 0:ℝ) ∧
    w (13/20) 0-(endpoint 0:ℝ)<errorBound at h0
  change -(errorBound:ℝ)<w (13/20) 1-(endpoint 1:ℝ) ∧
    w (13/20) 1-(endpoint 1:ℝ)<errorBound at h1
  have he : (0:ℝ)<(endpoint 0:ℝ)-errorBound ∧ 0<(endpoint 1:ℝ)-errorBound ∧
      1<(radialLower:ℝ) ∧
      (radialLower:ℝ)^2<((endpoint 0:ℝ)-errorBound)^2+((endpoint 1:ℝ)-errorBound)^2 ∧
      ((endpoint 0:ℝ)+errorBound)^2+((endpoint 1:ℝ)+errorBound)^2<(radialUpper:ℝ)^2 ∧
      0<(radialUpper:ℝ) := by exact_mod_cast endpoint_checked
  have hs : (radius (w (13/20)))^2=w (13/20) 0^2+w (13/20) 1^2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hx : (endpoint 0:ℝ)-errorBound<w (13/20) 0 := by linarith [h0.1]
  have hy : (endpoint 1:ℝ)-errorBound<w (13/20) 1 := by linarith [h1.1]
  have hx' : w (13/20) 0<(endpoint 0:ℝ)+errorBound := by linarith [h0.2]
  have hy' : w (13/20) 1<(endpoint 1:ℝ)+errorBound := by linarith [h1.2]
  constructor
  · have hsq0 := sq_le_sq₀ he.1.le (by linarith : 0≤w (13/20) 0)
    have hsq1 := sq_le_sq₀ he.2.1.le (by linarith : 0≤w (13/20) 1)
    nlinarith [hsq0.mpr hx.le,hsq1.mpr hy.le,hr (13/20)]
  · have hsq0 := sq_le_sq₀ (by linarith : 0≤w (13/20) 0)
      (by linarith : 0≤(endpoint 0:ℝ)+errorBound)
    have hsq1 := sq_le_sq₀ (by linarith : 0≤w (13/20) 1)
      (by linarith : 0≤(endpoint 1:ℝ)+errorBound)
    nlinarith [hsq0.mpr hx'.le,hsq1.mpr hy'.le]

theorem error_in_metres : (7000000:ℚ)*errorBound<1/10^9 := by decide +kernel
theorem radial_increase_metres :
    (7712524/1000000:ℚ)<7000000*(radialLower-1) ∧
      7000000*(radialUpper-1)<7712531/1000000 := by decide +kernel

end GNC.OrbitalComparison.TangentialReference
