/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode220
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e221 : NestedArithmetic.Expr 3 := .scaled (-1) e220
noncomputable def p221 : NestedHorner.Poly 3 := [[[98],[0],[0]],[[0,0],[0,0],[0]],[[3038,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[43218,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[373968,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[2199708,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[9311372,147,0],[147,0],[0]],[[0,0,0],[0,0],[0]],[[29293082,3283,0],[3283,0],[0]],[[0,0,0],[0,0],[0]],[[69745522,32585,0],[32585,0],[0]],[[0,0,0],[0,0],[0]],[[126798672,189434,0],[189434,0],[0]],[[0,0,0],[0,0],[0]],[[176299942,715841,0],[715841,0],[0]],[[0,0,0],[0,0],[0]],[[186513894,1845291,49],[1845291,98],[49]],[[0,0,0],[0,0],[0]],[[148279684,3314164,686],[3314164,1372],[686]],[[0,0,0],[0,0],[0]],[[86661204,4161913,3969],[4161913,7938],[3969]],[[0,0,0],[0,0],[0]],[[35907984,3612427,12250],[3612427,24500],[12250]],[[0,0,0],[0,0],[0]],[[9919854,2104550,21756],[2104550,43512],[21756]],[[0,0,0],[0,0],[0]],[[1627290,777483,22442],[777483,44884],[22442]],[[0,0,0],[0,0],[0]],[[119070,162729,12985],[162729,25970],[12985]],[[0,0,0],[0,0],[0]],[[0,14553,3822],[14553,7644],[3822]],[[0,0,0],[0,0],[0]],[[0,0,441],[0,882],[441]]]
theorem step221 : p221=NestedHorner.scale (-1) p220 := by decide +kernel
#print axioms step221
theorem h221 : NestedArithmetic.compile e221=p221 := StagedExprCompile.compile_scaled (-1) e221 e220 p220 p221 rfl h220 step221
#print axioms h221
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
