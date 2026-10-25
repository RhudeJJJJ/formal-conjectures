/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode194
import Proofs.RadenkovicGutmanD29Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[116],[0]],[[0,0],[0]],[[1740,0],[0]],[[0,0],[0]],[[10904,0],[0]],[[0,0],[0]],[[37004,0],[0]],[[0,0],[0]],[[73776,0],[0]],[[0,0],[0]],[[87812,58],[58]],[[0,0],[0]],[[60552,406],[406]],[[0,0],[0]],[[21924,928],[928]],[[0,0],[0]],[[3132,754],[754]],[[0,0],[0]],[[0,174],[174]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
