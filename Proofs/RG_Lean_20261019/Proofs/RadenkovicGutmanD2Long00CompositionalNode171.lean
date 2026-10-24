/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode163
import Proofs.RadenkovicGutmanD2Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .plus e163 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[0],[0]],[[0,0],[0]],[[12,0],[0,0]],[[0,0],[0,0]],[[172,0],[0,0]],[[0,0],[0,0]],[[1024,0],[0,0]],[[0,0],[0,0]],[[3276,0],[0,0]],[[0,0],[0,0]],[[6096,0],[0,0]],[[0,0],[0,0]],[[6692,2],[2,0]],[[0,0],[0,0]],[[4208,14],[14,0]],[[0,0],[0,0]],[[1380,32],[32,0]],[[0,0],[0,0]],[[180,26],[26,0]],[[0,0],[0,0]],[[0,6],[6,0]]]
theorem step171 : p171=NestedHorner.add p163 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_plus e171 e163 e170 p163 p170 p171 rfl h163 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
