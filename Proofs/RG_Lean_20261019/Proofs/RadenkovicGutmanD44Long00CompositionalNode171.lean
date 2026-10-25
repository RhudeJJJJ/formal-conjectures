/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode030
import Proofs.RadenkovicGutmanD44Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .times e030 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[88],[0]],[[0,0],[0]],[[1320,0],[0]],[[0,0],[0]],[[8272,0],[0]],[[0,0],[0]],[[28072,0],[0]],[[0,0],[0]],[[55968,0],[0]],[[0,0],[0]],[[66616,44],[44]],[[0,0],[0]],[[45936,308],[308]],[[0,0],[0]],[[16632,704],[704]],[[0,0],[0]],[[2376,572],[572]],[[0,0],[0]],[[0,132],[132]]]
theorem step171 : p171=NestedArithmetic.mul p030 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_times e171 e030 e170 p030 p170 p171 rfl h030 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
