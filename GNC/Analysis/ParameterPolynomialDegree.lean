import GNC.Analysis.ParameterPolynomial
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval

/-! A sparse coefficient record really is a polynomial of the advertised
transverse-input degree. Time is fixed but arbitrary; no numerical fitting
assumption is used. The degree estimates are mathlib's polynomial theorems. -/
namespace GNC.ParameterPolynomial
noncomputable section

def spatialTerm (a : Term) (t : ℝ) : MvPolynomial (Fin 3) ℝ :=
  MvPolynomial.C (PolynomialOrder.value a.time t)*
    MvPolynomial.X 0^a.u*MvPolynomial.X 1^a.v*MvPolynomial.X 2^a.c

def spatialPolynomial : Coefficients → ℝ → MvPolynomial (Fin 3) ℝ
  | [],_ => 0
  | a::p,t => spatialTerm a t+spatialPolynomial p t

theorem spatialTerm_degree (a : Term) (t : ℝ) :
    (spatialTerm a t).totalDegree≤a.u+a.v+a.c := by
  have h1 : (MvPolynomial.C (PolynomialOrder.value a.time t)*
      (MvPolynomial.X 0: MvPolynomial (Fin 3) ℝ)^a.u).totalDegree≤a.u := by
    simpa using MvPolynomial.totalDegree_mul
      (MvPolynomial.C (PolynomialOrder.value a.time t):MvPolynomial (Fin 3) ℝ)
      (MvPolynomial.X 0^a.u)
  have h2 := MvPolynomial.totalDegree_mul
    (MvPolynomial.C (PolynomialOrder.value a.time t)*
      (MvPolynomial.X 0: MvPolynomial (Fin 3) ℝ)^a.u) (MvPolynomial.X 1^a.v)
  have h3 := MvPolynomial.totalDegree_mul
    (MvPolynomial.C (PolynomialOrder.value a.time t)*
      (MvPolynomial.X 0: MvPolynomial (Fin 3) ℝ)^a.u*MvPolynomial.X 1^a.v)
    (MvPolynomial.X 2^a.c)
  simp only [MvPolynomial.totalDegree_X_pow] at h2 h3
  exact h3.trans (Nat.add_le_add_right (h2.trans (Nat.add_le_add_right h1 _)) _)

theorem spatialPolynomial_degree (p : Coefficients) (t : ℝ) (d : ℕ)
    (h : ∀ a ∈ p, a.u+a.v+a.c≤d) :
    (spatialPolynomial p t).totalDegree≤d := by
  induction p with
  | nil => simp [spatialPolynomial]
  | cons a p ih =>
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le
      ((spatialTerm_degree a t).trans (h a (by simp)))
      (ih (fun b hb => h b (by simp [hb]))))

theorem spatialPolynomial_value (p : Coefficients) (x : Fin 3 → ℝ) (t : ℝ) :
    MvPolynomial.eval x (spatialPolynomial p t)=value p x t := by
  induction p with
  | nil => simp [spatialPolynomial]
  | cons a p ih =>
    simp [spatialPolynomial,spatialTerm,termValue,monomial,ih,mul_assoc]

def transverseTerm (a : Term) (t : ℝ) : MvPolynomial (Fin 2) ℝ :=
  MvPolynomial.C (PolynomialOrder.value a.time t)*
    MvPolynomial.X 0^a.u*MvPolynomial.X 1^a.v

def transversePolynomial : Coefficients → ℝ → MvPolynomial (Fin 2) ℝ
  | [],_ => 0
  | a::p,t => transverseTerm a t+transversePolynomial p t

theorem transverseTerm_degree (a : Term) (t : ℝ) :
    (transverseTerm a t).totalDegree≤a.u+a.v := by
  let C : MvPolynomial (Fin 2) ℝ := MvPolynomial.C (PolynomialOrder.value a.time t)
  let U : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 0^a.u
  let V : MvPolynomial (Fin 2) ℝ := MvPolynomial.X 1^a.v
  have hu : (C*U).totalDegree≤a.u := by
    simpa [C,U] using MvPolynomial.totalDegree_mul C U
  have hv : V.totalDegree=a.v := by simp [V]
  exact (MvPolynomial.totalDegree_mul (C*U) V).trans
    (by simpa only [hv] using Nat.add_le_add_right hu V.totalDegree)

theorem transversePolynomial_degree (p : Coefficients) (t : ℝ) (d : ℕ)
    (h : ∀ a ∈ p, a.u+a.v≤d) :
    (transversePolynomial p t).totalDegree≤d := by
  induction p with
  | nil => simp [transversePolynomial]
  | cons a p ih =>
    exact (MvPolynomial.totalDegree_add _ _).trans (max_le
      ((transverseTerm_degree a t).trans (h a (by simp)))
      (ih (fun b hb => h b (by simp [hb]))))

theorem transversePolynomial_value (p : Coefficients) (x : Fin 3 → ℝ) (t : ℝ)
    (h : ∀ a ∈ p, a.c=0) :
    MvPolynomial.eval ![x 0,x 1] (transversePolynomial p t)=value p x t := by
  induction p with
  | nil => simp [transversePolynomial]
  | cons a p ih =>
    have ha := h a (by simp)
    have hp := ih (fun b hb => h b (by simp [hb]))
    simp [transversePolynomial,transverseTerm,termValue,monomial,ha,hp,mul_assoc]

end
end GNC.ParameterPolynomial
