import GNC.Applications.OrbitalComparison.CenteredResponseInitial
import GNC.Applications.OrbitalComparison.CenteredResponseData.Envelope
import GNC.Dynamics.QuadraticResponseCertificate

/-! Non-iterative sizes of the actual computed response curves. The
small midpoint initial data and rotation-induced forcing are proved,
and both computed response defects are charged in their growth bounds. -/
noncomputable section
namespace GNC.OrbitalComparison.CenteredResponseData
open CartesianResponsePolynomial Matrix Set

theorem first_response_derivative (w : Fin 8 → ℝ) (t : ℝ) :
    HasDerivAt (firstResponse w) (firstVelocity w t) t := by
  have he : firstResponse w=response first w := funext (first_response_value w)
  rw [he]
  exact response_derivative first w t

theorem first_velocity_derivative (w : Fin 8 → ℝ) (t : ℝ) :
    HasDerivAt (firstVelocity w) (firstAcceleration w t) t :=
  response_derivative (fun j => derivative (first j)) w t

theorem second_response_derivative (w : Fin 8 → ℝ) (t : ℝ) :
    HasDerivAt (secondResponse w) (secondVelocity w t) t := by
  have he : secondResponse w=response second (productWeights w) := funext (second_response_value w)
  rw [he]
  exact response_derivative second (productWeights w) t

theorem second_velocity_derivative (w : Fin 8 → ℝ) (t : ℝ) :
    HasDerivAt (secondVelocity w) (secondAcceleration w t) t :=
  response_derivative (fun j => derivative (second j)) (productWeights w) t

theorem first_response_continuous (w : Fin 8 → ℝ) : Continuous (firstResponse w) :=
  continuous_iff_continuousAt.mpr fun t => (first_response_derivative w t).continuousAt
theorem first_velocity_continuous (w : Fin 8 → ℝ) : Continuous (firstVelocity w) :=
  continuous_iff_continuousAt.mpr fun t => (first_velocity_derivative w t).continuousAt
theorem second_response_continuous (w : Fin 8 → ℝ) : Continuous (secondResponse w) :=
  continuous_iff_continuousAt.mpr fun t => (second_response_derivative w t).continuousAt
theorem second_velocity_continuous (w : Fin 8 → ℝ) : Continuous (secondVelocity w) :=
  continuous_iff_continuousAt.mpr fun t => (second_velocity_derivative w t).continuousAt

theorem response_data_real : 0 ≤ (responseGain:ℝ) ∧ (responseGain:ℝ) < 2 ∧
    0 ≤ (firstInitialRadius:ℝ) ∧ 0 ≤ (firstInitialSpeed:ℝ) ∧ 0 ≤ (inputMagnitude:ℝ) ∧
    0 ≤ (firstDefect:ℝ) ∧ 0 ≤ (secondDefect:ℝ) := by exact_mod_cast response_data_nonnegative

theorem input_magnitude_cast : (inputMagnitude:ℝ)=(1/20)*(forceFactor:ℝ) := by
  simp only [inputMagnitude,Rat.cast_div,Rat.cast_ofNat]
  ring

theorem first_acceleration_bound (φ : Vec3) (hφ : enorm φ≤1/10)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖firstAcceleration (rotationWeights φ) t‖≤
      (responseGain:ℝ)*‖firstResponse (rotationWeights φ) t‖+
        ((inputMagnitude:ℝ)+(firstDefect:ℝ)) := by
  have hk : (0:ℝ)≤K := by exact_mod_cast K_nonnegative
  have hu : ‖(1:ℝ) • forceDifference φ t‖≤(inputMagnitude:ℝ) := by
    simpa only [one_smul,input_magnitude_cast] using rotation_force_bound φ hφ ht
  have he := first_rotation_defect φ hφ ht
  rw [norm_sub_rev] at he
  have hb := Gravity.computed_linear_response_acceleration (K:ℝ) 1 hk (by norm_num)
    (nominal t) (firstResponse (rotationWeights φ) t) (firstAcceleration (rotationWeights φ) t)
    (forceDifference φ t) (r := 1) (by norm_num) (by rw [nominal_norm]) hu
    (by simpa only [one_smul] using he)
  simpa only [responseGain,Rat.cast_mul,Rat.cast_ofNat,one_pow,div_one,one_mul] using hb

theorem first_response_bound (φ : Vec3) (hφ : enorm φ≤1/10)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖firstResponse (rotationWeights φ) t‖≤(firstRange:ℝ) := by
  obtain ⟨hκ,hk,ha,hb,hu,he,_⟩ := response_data_real
  have hip : ‖firstResponse (rotationWeights φ) 0‖≤(firstInitialRadius:ℝ) := by
    convert first_initial_bound φ hφ using 1
    norm_num [firstInitialRadius]
  have hiv : ‖firstVelocity (rotationWeights φ) 0‖≤(firstInitialSpeed:ℝ) := by
    convert first_velocity_initial_bound φ hφ using 1
    norm_num [firstInitialSpeed]
  have hf := add_nonneg hu he
  have h := QuadraticMajorant.response
    (firstResponse (rotationWeights φ)) (firstVelocity (rotationWeights φ))
    (firstAcceleration (rotationWeights φ)) hκ hk ha hb hf
    (first_response_continuous _) (first_velocity_continuous _)
    (fun s _ => first_response_derivative _ s) (fun s _ => first_velocity_derivative _ s)
    hip hiv (fun s hs => first_acceleration_bound φ hφ hs) t ht
  have hend := (QuadraticMajorant.bounds hκ hk ha hb hf ht).1
  have hr := (Rat.cast_le (K := ℝ)).mpr first_range_checked
  simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_sub,Rat.cast_ofNat] at hr
  have hm : QuadraticMajorant.value (responseGain:ℝ) (firstInitialRadius:ℝ)
      (firstInitialSpeed:ℝ) ((inputMagnitude:ℝ)+(firstDefect:ℝ)) 1≤(firstRange:ℝ) := by
    simpa only [QuadraticMajorant.value,QuadraticMajorant.coefficient,one_pow,mul_one,add_assoc] using hr
  exact h.1.trans (hend.trans hm)

theorem second_acceleration_bound (φ : Vec3) (hφ : enorm φ≤1/10)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖secondAcceleration (rotationWeights φ) t‖≤
      (responseGain:ℝ)*‖secondResponse (rotationWeights φ) t‖+
        (3*(K:ℝ)*(firstRange:ℝ)^2+(secondDefect:ℝ)) := by
  have hk : (0:ℝ)≤K := by exact_mod_cast K_nonnegative
  have he := second_rotation_defect φ hφ ht
  rw [norm_sub_rev] at he
  have hb := Gravity.computed_quadratic_response_acceleration (K:ℝ) 1 hk (by norm_num)
    (nominal t) (firstResponse (rotationWeights φ) t) (secondResponse (rotationWeights φ) t)
    (secondAcceleration (rotationWeights φ) t) (r := 1) (by norm_num) (by rw [nominal_norm])
    (first_response_bound φ hφ ht) (by simpa only [one_smul] using he)
  simpa only [responseGain,Rat.cast_mul,Rat.cast_ofNat,one_pow,div_one,one_mul] using hb

theorem second_response_bound (φ : Vec3) (hφ : enorm φ≤1/10)
    {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    ‖secondResponse (rotationWeights φ) t‖≤(secondRange:ℝ) := by
  obtain ⟨hκ,hk,_,_,_,_,he⟩ := response_data_real
  have hK : (0:ℝ)≤K := by exact_mod_cast K_nonnegative
  have hf : 0≤3*(K:ℝ)*(firstRange:ℝ)^2+(secondDefect:ℝ) := by positivity
  have h := QuadraticMajorant.response
    (secondResponse (rotationWeights φ)) (secondVelocity (rotationWeights φ))
    (secondAcceleration (rotationWeights φ)) hκ hk (by norm_num : (0:ℝ)≤0)
    (by norm_num : (0:ℝ)≤0) hf
    (second_response_continuous _) (second_velocity_continuous _)
    (fun s _ => second_response_derivative _ s) (fun s _ => second_velocity_derivative _ s)
    (by rw [second_initial_value,norm_zero]) (by rw [second_initial_velocity_value,norm_zero])
    (fun s hs => second_acceleration_bound φ hφ hs) t ht
  have hend := (QuadraticMajorant.bounds hκ hk (by norm_num : (0:ℝ)≤0)
    (by norm_num : (0:ℝ)≤0) hf ht).1
  have hr := (Rat.cast_le (K := ℝ)).mpr second_range_checked
  simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_sub,Rat.cast_pow,Rat.cast_ofNat] at hr
  have hm : QuadraticMajorant.value (responseGain:ℝ) 0 0
      (3*(K:ℝ)*(firstRange:ℝ)^2+(secondDefect:ℝ)) 1≤(secondRange:ℝ) := by
    simpa only [QuadraticMajorant.value,QuadraticMajorant.coefficient,one_pow,mul_one,
      add_zero,zero_mul,mul_zero,zero_add] using hr
  exact h.1.trans (hend.trans hm)

end GNC.OrbitalComparison.CenteredResponseData
