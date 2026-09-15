import GNC.Applications.OrbitalFuel.BurnMeanResponse

/-! Convert the exact switched response to the very same terminal RTN/SI
matrix used in the fuel program. This final map is linear in the relative
position/velocity and command vectors; no force linearization is made here.
-/
noncomputable section
open Matrix
namespace GNC.Applications.OrbitalFuel.TerminalResponse
open GNC PolynomialOrbitTransition ChaserResponse BurnMeanResponse

def output (z : Fin 5 → ℝ) (speed : ℝ) (p : Fin 4 → ℝ) (n : Fin 2 → ℝ)
    (i : Fin 6) : ℝ :=
  ![(FreeResponse.lengthUnit:ℝ)*(z 0*z 4*p 0+z 1*z 4*p 1),
    (FreeResponse.lengthUnit:ℝ)*(-z 1*z 4*p 0+z 0*z 4*p 1),
    (FreeResponse.lengthUnit:ℝ)*n 0,
    speed*(z 0*z 4*p 2+z 1*z 4*p 3), speed*(-z 1*z 4*p 2+z 0*z 4*p 3),speed*n 1] i /
      (FreeResponse.tolerance i:ℝ)

theorem output_zero (z : Fin 5 → ℝ) (speed : ℝ) : output z speed 0 0 = 0 := by
  ext i
  fin_cases i <;> simp [output, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail]

theorem output_add (z : Fin 5 → ℝ) (speed : ℝ) (p q : Fin 4 → ℝ) (n m : Fin 2 → ℝ) :
    output z speed (p+q) (n+m) = output z speed p n+output z speed q m := by
  ext i
  fin_cases i <;> simp [output, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail] <;> ring

theorem output_sum {ι : Type*} [Fintype ι] (z : Fin 5 → ℝ) (speed : ℝ)
    (p : ι → Fin 4 → ℝ) (n : ι → Fin 2 → ℝ) :
    output z speed (∑ j, p j) (∑ j, n j) = ∑ j, output z speed (p j) (n j) := by
  classical
  have h (s : Finset ι) : output z speed (∑ j ∈ s, p j) (∑ j ∈ s, n j) =
      ∑ j ∈ s, output z speed (p j) (n j) := by
    induction s using Finset.induction_on with
    | empty => simp [output_zero]
    | @insert j s hj ih => simp [Finset.sum_insert, hj, output_add, ih]
  exact h Finset.univ

set_option maxHeartbeats 4000000 in
theorem output_burn (z : Fin 5 → ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (speed : ℝ) (means : Fin 10 → ℝ) (q : Vec3) :
    output z speed
      (F *ᵥ ((BurnSensitivity.burnScale:ℝ) •
        (Matrix.of (fun (i : Fin 4) (k : Fin 2) => means ⟨2*i.val+k.val,by omega⟩) *ᵥ ![q 0,q 1])))
      (H *ᵥ (((BurnSensitivity.burnScale:ℝ)*q 2) • (fun (i : Fin 2) => means ⟨8+i.val,by omega⟩))) =
      BurnSensitivity.physicalMatrix z F H speed means *ᵥ q := by
  ext i
  fin_cases i <;>
    norm_num [output, BurnSensitivity.physicalMatrix, BurnSensitivity.normalizedMatrix,
      Matrix.mulVec, Matrix.mul_apply, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.vecHead, Matrix.vecTail]
  all_goals ring_nf <;> simp <;> ring

def initialPlane (initialSpeed : ℝ) : Fin 4 → ℝ :=
  ![0,-10000000/(FreeResponse.lengthUnit:ℝ),
    (5/4)*initialSpeed*(10000000/(FreeResponse.lengthUnit:ℝ)),0]

def initialNormal : Fin 2 → ℝ := ![1000000/(FreeResponse.lengthUnit:ℝ),0]

theorem output_free (z : Fin 5 → ℝ) (F : Matrix (Fin 4) (Fin 4) ℝ)
    (H : Matrix (Fin 2) (Fin 2) ℝ) (speed initialSpeed : ℝ) (integrals : Fin 4 → ℝ) :
    output z speed (F *ᵥ (initialPlane initialSpeed-(FreeResponse.alpha:ℝ) • integrals))
      (H *ᵥ initialNormal) =
    fun i => FreeResponse.physicalOutput z F H speed initialSpeed integrals i/(FreeResponse.tolerance i:ℝ) := by
  ext i
  fin_cases i <;>
    simp [output, initialPlane, initialNormal, FreeResponse.physicalOutput,
      Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.vecHead, Matrix.vecTail]

/-- The retained switched trajectory, after terminal RTN and SI conversion,
is exactly the affine terminal map used by the certified fuel program. -/
theorem retained_output (z : ℝ → Fin 5 → ℝ)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hz : Continuous z) (hF : Continuous F) (hH : Continuous H)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt F (planeGenerator (z t)*F t) t)
    (hdH : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt H (normalGenerator (z t)*H t) t)
    (hiF : F 0 = 1) (hiH : H 0 = 1) (speed initialSpeed : ℝ) (command : Fin 18 → Vec3) :
    output (z (3/5)) speed
      (retainedPlane (FreeResponse.alpha:ℝ) (50*(BurnSensitivity.burnScale:ℝ)) z F
        (initialPlane initialSpeed) command)
      (retainedNormal (50*(BurnSensitivity.burnScale:ℝ)) H initialNormal command) =
    (fun i => FreeResponse.physicalOutput (z (3/5)) (F (3/5)) (H (3/5)) speed initialSpeed
      (FreeResponse.pullbackIntegrals z F) i/(FreeResponse.tolerance i:ℝ))+
      ∑ j : Fin 18, BurnSensitivity.physicalMatrix (z (3/5)) (F (3/5)) (H (3/5)) speed
        (BurnSensitivity.means z F H j) *ᵥ command j := by
  rw [retained_plane_means _ _ z F H hz hF hdF hiF,
    retained_normal_means _ z F H hH hdH hiH]
  have hscale : 50*(BurnSensitivity.burnScale:ℝ)/50 = (BurnSensitivity.burnScale:ℝ) := by ring
  simp only [hscale]
  have hsplit : initialPlane initialSpeed+
      (∑ j : Fin 18, (BurnSensitivity.burnScale:ℝ) •
        (planeMean z F H j *ᵥ ![command j 0,command j 1]))-
      (FreeResponse.alpha:ℝ) • FreeResponse.pullbackIntegrals z F =
      (initialPlane initialSpeed-(FreeResponse.alpha:ℝ) • FreeResponse.pullbackIntegrals z F)+
      ∑ j : Fin 18, (BurnSensitivity.burnScale:ℝ) •
        (planeMean z F H j *ᵥ ![command j 0,command j 1]) := by abel
  rw [hsplit, mulVec_add, mulVec_add, output_add, output_free,
    mulVec_sum, mulVec_sum, output_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact output_burn (z (3/5)) (F (3/5)) (H (3/5)) speed (BurnSensitivity.means z F H j) (command j)

/-- Exact terminal-map correspondence for an existing nonlinear trajectory
with the prescribed constant-acceleration burns. The last summand is the
transported gravity remainder, not a discarded approximation. -/
theorem nonlinear_endpoint (w : ℝ → Fin 4 → ℝ) (p v : ℝ → Vec3)
    (F : ℝ → Matrix (Fin 4) (Fin 4) ℝ) (H : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (command : Fin 18 → Vec3) (speed initialSpeed : ℝ)
    (hw : Continuous w) (hp : Continuous p) (hv : Continuous v)
    (hz : Continuous (fun t => PolynomialOrbit.lift (w t))) (hF : Continuous F) (hH : Continuous H)
    (hr : ∀ t ∈ Set.Icc (0:ℝ) (3/5), 0 < PolynomialOrbit.radius (w t))
    (hn : ∀ t ∈ Set.Icc (0:ℝ) (3/5), p t ≠ 0)
    (hdw : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt w (PolynomialOrbit.physicalRate
      (FreeResponse.alpha:ℝ) (w t)) t)
    (hdF : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt F (planeGenerator (PolynomialOrbit.lift (w t))*F t) t)
    (hdH : ∀ t ∈ Set.Icc (0:ℝ) (3/5), HasDerivAt H (normalGenerator (PolynomialOrbit.lift (w t))*H t) t)
    (hiF : F 0 = 1) (hiH : H 0 = 1)
    (hip : PlanarChaserError.plane (w 0) (p 0) (v 0) = initialPlane initialSpeed)
    (hin : PlanarChaserError.normal (p 0) (v 0) = initialNormal)
    (hdp : ∀ k < 37, ∀ t ∈ Set.Ioo (BurnSchedule.time k:ℝ) (BurnSchedule.time (k+1):ℝ),
      HasDerivAt p (v t) t)
    (hdv : ∀ k < 37, ∀ t ∈ Set.Ioo (BurnSchedule.time k:ℝ) (BurnSchedule.time (k+1):ℝ),
      HasDerivAt v (Gravity.field3 1 (p t)+BurnSchedule.input
        (fun j t => acceleration (50*(BurnSensitivity.burnScale:ℝ))
          (PolynomialOrbit.lift (w t)) (command j)) k t) t) :
    output (PolynomialOrbit.lift (w (3/5))) speed
      (PlanarChaserError.plane (w (3/5)) (p (3/5)) (v (3/5)))
      (PlanarChaserError.normal (p (3/5)) (v (3/5))) =
    ((fun i => FreeResponse.physicalOutput (PolynomialOrbit.lift (w (3/5))) (F (3/5)) (H (3/5))
      speed initialSpeed (FreeResponse.pullbackIntegrals (fun t => PolynomialOrbit.lift (w t)) F) i/
        (FreeResponse.tolerance i:ℝ))+
      ∑ j : Fin 18, BurnSensitivity.physicalMatrix (PolynomialOrbit.lift (w (3/5))) (F (3/5)) (H (3/5))
        speed (BurnSensitivity.means (fun t => PolynomialOrbit.lift (w t)) F H j) *ᵥ command j)+
      output (PolynomialOrbit.lift (w (3/5))) speed
        (planeRemainder F (fun t => PlanarChaserError.residual (w t) (p t)))
        (normalRemainder H (fun t => PlanarChaserError.residual (w t) (p t))) := by
  have he := ChaserResponse.plane_endpoint (FreeResponse.alpha:ℝ) (50*(BurnSensitivity.burnScale:ℝ))
    w p v F command hw hp hv hz hF hr hn hdw hdF hiF hdp hdv
  have hn' := ChaserResponse.normal_endpoint (50*(BurnSensitivity.burnScale:ℝ))
    w p v H command hw hp hv hH hr hn hdH hiH hdp hdv
  rw [he, hn', hip, hin, output_add,
    retained_output (fun t => PolynomialOrbit.lift (w t)) F H hz hF hH hdF hdH hiF hiH]

end GNC.Applications.OrbitalFuel.TerminalResponse
