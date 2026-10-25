/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode030
import Proofs.RadenkovicGutmanD32Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[64],[0]],[[0,0],[0]],[[960,0],[0]],[[0,0],[0]],[[6016,0],[0]],[[0,0],[0]],[[20416,0],[0]],[[0,0],[0]],[[40704,0],[0]],[[0,0],[0]],[[48448,32],[32]],[[0,0],[0]],[[33408,224],[224]],[[0,0],[0]],[[12096,512],[512]],[[0,0],[0]],[[1728,416],[416]],[[0,0],[0]],[[0,96],[96]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
