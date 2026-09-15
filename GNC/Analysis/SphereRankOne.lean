import GNC.Analysis.SphereResponse
import GNC.Analysis.DiskPolynomial
import GNC.Planning.FlopKernel

/-! Preserve sphere curvature before compressing a quadratic response.
The omitted terms are explicit; retaining a single quadratic direction is
not claimed to be exact. This representation can be used by ordinary STTs. -/
namespace GNC.SphereRankOne
noncomputable section
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def compressed (u v c : ℝ) (U V C Uu Vv : E) : E :=
  u • U+v • V+c • (C+2 • Vv)+u^2 • (Uu-Vv)

theorem decomposition (u v c : ℝ) (hs : u^2+v^2=2*c-c^2)
    (U V C Uu Uv Vv Cu Cv Cc : E) :
    SphereResponse.quadratic u v c U V C Uu Uv Vv Cu Cv Cc=
      compressed u v c U V C Uu Vv+
        (u*v) • Uv+(c*u) • Cu+(c*v) • Cv+c^2 • (Cc-Vv) := by
  have hv : v^2=2*c-c^2-u^2 := by linarith
  unfold SphereResponse.quadratic compressed
  rw [hv]
  module

/-- Bounding planar and normal polynomial errors separately avoids charging
their sum as a vector norm. Both supplied polynomial certificates are checked. -/
theorem split_bound (p : DiskPolynomial.Vector 3)
    (P : DiskPolynomial.Certificate 2) (N : DiskPolynomial.Certificate 1)
    {σ C BP BN B : ℚ}
    (hP : P.Valid (fun i => p i.castSucc) σ C BP)
    (hN : N.Valid (fun _ => p 2) σ C BN)
    (hσ : 0≤σ) (hBP : 0≤BP) (hBN : 0≤BN)
    (hB : 0≤B) (hs : BP^2+BN^2≤B^2)
    {x : Fin 3 → ℝ} (hx : x 0^2+x 1^2≤(σ:ℝ)^2) (hc : |x 2|≤(C:ℝ))
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ‖DiskPolynomial.vectorValue p x t‖≤(B:ℝ) := by
  have hp := P.certifies _ hP hσ hx hc ht
  have hn := N.certifies _ hN hσ hx hc ht
  have he : ‖DiskPolynomial.vectorValue p x t‖^2=
      ‖DiskPolynomial.vectorValue (fun i : Fin 2 => p i.castSucc) x t‖^2+
      ‖DiskPolynomial.vectorValue (fun _ : Fin 1 => p 2) x t‖^2 := by
    simp [EuclideanSpace.real_norm_sq_eq,DiskPolynomial.vectorValue,
      Fin.sum_univ_three,Fin.sum_univ_two,add_assoc]
  have hp0 := norm_nonneg (DiskPolynomial.vectorValue (fun i : Fin 2 => p i.castSucc) x t)
  have hn0 := norm_nonneg (DiskPolynomial.vectorValue (fun _ : Fin 1 => p 2) x t)
  have hpr : (0:ℝ)≤BP := by exact_mod_cast hBP
  have hnr : (0:ℝ)≤BN := by exact_mod_cast hBN
  have hbr : (0:ℝ)≤B := by exact_mod_cast hB
  have hsr : (BP:ℝ)^2+(BN:ℝ)^2≤(B:ℝ)^2 := by exact_mod_cast hs
  nlinarith [sq_le_sq₀ hp0 hpr |>.2 hp,sq_le_sq₀ hn0 hnr |>.2 hn,
    norm_nonneg (DiskPolynomial.vectorValue p x t)]

end

open Planning.FlopKernel
variable {K : Type*} [CommSemiring K]

/-- A factored planar output, given the physical direction components.
Time-coefficient generation, direction construction and loads are separate. -/
def queryComponent (u c L C Q : K) : Value K :=
  add (mul (input u) (add (input L) (mul (input u) (input Q))))
    (mul (input c) (input C))

theorem queryComponent_value (u c L C Q : K) :
    (queryComponent u c L C Q).value=L*u+C*c+Q*u^2 := by
  simp only [queryComponent,Planning.FlopKernel.add,Planning.FlopKernel.mul,input]
  ring

theorem queryComponent_flops (u c L C Q : K) :
    (queryComponent u c L C Q).flops=5 := rfl

/-- Two planar outputs and one linear normal output: eleven scalar adds/
multiplies. An FMA counts as two. This is an algorithm count, not a lower bound. -/
theorem spatial_query_flops (u v c L0 C0 Q0 L1 C1 Q1 V : K) :
    (queryComponent u c L0 C0 Q0).flops+(queryComponent u c L1 C1 Q1).flops+
      (mul (input v) (input V)).flops=11 := rfl

end GNC.SphereRankOne
