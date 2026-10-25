/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode194
import Proofs.RadenkovicGutmanD16Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e195 : NestedArithmetic.Expr 3 := .times e194 e170
noncomputable def p195 : NestedHorner.Poly 3 := [[[64],[0]],[[0,0],[0]],[[960,0],[0]],[[0,0],[0]],[[6016,0],[0]],[[0,0],[0]],[[20416,0],[0]],[[0,0],[0]],[[40704,0],[0]],[[0,0],[0]],[[48448,32],[32]],[[0,0],[0]],[[33408,224],[224]],[[0,0],[0]],[[12096,512],[512]],[[0,0],[0]],[[1728,416],[416]],[[0,0],[0]],[[0,96],[96]]]
theorem step195 : p195=NestedArithmetic.mul p194 p170 := by decide +kernel
#print axioms step195
theorem h195 : NestedArithmetic.compile e195=p195 := StagedExprCompile.compile_times e195 e194 e170 p194 p170 p195 rfl h194 h170 step195
#print axioms h195
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
