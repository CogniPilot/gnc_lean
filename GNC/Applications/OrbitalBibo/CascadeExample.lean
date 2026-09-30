import GNC.Control.OrbitalCascadeTube
import GNC.Control.AttitudeThrustBridge
import Mathlib.Analysis.Real.Pi.Bounds

/-! Exact design data for a synthetic constant-acceleration powered tracking
case. SI quantities: radius floor 40 Mm, position scale 100 m, response time
1000 s, corridor 12 m, nominal acceleration 0.2 mm/s², angle cap 0.02 rad,
external acceleration 1 micrometre/s². These are design choices, not flight
specifications. This checks the numerical obligations; reference existence,
reference radius, model realization and actuator assumptions remain separate.
-/
namespace GNC.OrbitalBibo.CascadeExample
noncomputable section
def mu : ℝ := 398600441800000
def radius : ℝ := 40000000
def corridor : ℝ := 12
def scale : ℝ := 100
def responseTime : ℝ := 1000
def angle : ℝ := 1/50
def thrustAcceleration : ℝ := 1/5000
def accelerationError : ℝ := 1/1000000
def k : ℝ := 2*mu*responseTime^2/radius^3
def c : ℝ := 3*mu*responseTime^2*scale/(radius-corridor)^4
def R : ℝ := corridor/scale
def delta : ℝ := responseTime^2/scale*(thrustAcceleration*angle+accelerationError)
def beta : ℝ := 1/2-k-c*R

theorem gravity_domain : 0 < radius ∧ corridor < radius := by
  norm_num [radius,corridor]

theorem scaled_input : delta = 1/20 := by
  norm_num [delta,responseTime,scale,thrustAcceleration,angle,accelerationError]

theorem decay_and_budget : 0 < beta ∧ 2*delta^2 < beta*R^2 := by
  norm_num [beta,k,c,mu,responseTime,radius,corridor,scale,R,scaled_input]

theorem angle_chart : 0 ≤ angle ∧ angle < Real.pi := by
  constructor
  · norm_num [angle]
  · have h := Real.pi_gt_three
    norm_num [angle]
    linarith

/-- kq=kz=0.1/s, kappa=0.01/s², ell=cAtt=0.1/s,
angular acceleration disturbance <=0.0001 rad/s². -/
theorem torque_budget :
    (1/10000 : ℝ)^2/(2*(1/10)*(1/10)) ≤ (1/100)*angle^2/2 := by
  norm_num [angle]

/-- A 1 m position ball and zero velocity fit the translation energy tube. -/
theorem initial_budget : (2 : ℝ)*(1/scale)^2 ≤ R^2 := by
  norm_num [scale,R,corridor]

/-- For 100 kg mass the entire 12 m energy tube needs less than 3 mN of
ideal vector correction force. The exact squared gain is five. -/
theorem correction_force_budget :
    (100 : ℝ)^2*5*corridor^2/responseTime^4 < (3/1000 : ℝ)^2 := by
  norm_num [corridor,responseTime]

/-- Spherical inertia 10 kg m², constant reference rate <=0.0001/s,
and the proved inverse-Jacobian gain 4/3 on the one-radian chart.
The four terms bound reference transport, command-rate derivative,
rate feedback and angle feedback. This is an authority calculation,
not a reaction-wheel momentum-storage or flexible-body certificate. -/
theorem torque_authority_budget :
    (10 : ℝ)*((1/10000+(1/10)*angle+(1/10)*angle)*(1/10000)+
      (1/10)*((1/10)*angle+(4/3)*((1/10)*angle))+
      (1/10)*((1/10)*angle)+(1/100)*angle) < 2/100 := by
  norm_num [angle]

/-- The asymptotic position bound is below 10.2 m; this is a readable
rounding of the derived value, not slack used to close the invariant tube. -/
theorem asymptotic_position : scale^2*(2*delta^2/beta) < (102/10 : ℝ)^2 := by
  norm_num [scale,scaled_input,beta,k,c,mu,responseTime,radius,corridor,R]

/-- The actual inner-loop energy bound gives an ultimate angle radius of
0.01 rad, although the initial-energy chart cap is 0.02 rad. -/
theorem ultimate_angle_squared :
    (1/10000 : ℝ)^2/((1/100)*(1/10)*(1/10)) = (1/100 : ℝ)^2 := by
  norm_num

def ultimateDelta : ℝ := responseTime^2/scale*
  (thrustAcceleration*(1/100)+accelerationError)

/-- For this specified design, retaining the inner-loop transient reduces
the limiting squared position envelope by 9/25, hence its radius by 3/5.
This compares two certificates of the same controller, not two coordinates. -/
theorem ultimate_supply_ratio : 2*ultimateDelta^2 = (9/25 : ℝ)*(2*delta^2) := by
  norm_num [ultimateDelta,responseTime,scale,thrustAcceleration,accelerationError,scaled_input]

theorem refined_asymptotic_position : scale^2*(2*ultimateDelta^2/beta) < (61/10 : ℝ)^2 := by
  norm_num [ultimateDelta,scale,thrustAcceleration,accelerationError,
    beta,k,c,mu,responseTime,radius,corridor,R]

end
end GNC.OrbitalBibo.CascadeExample
