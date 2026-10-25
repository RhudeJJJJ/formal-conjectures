/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode171
import Proofs.RadenkovicGutmanD44Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[88,0],[0]],[[0,0],[0]],[[1320,0],[0]],[[0,0],[0]],[[8272,0],[0]],[[0,0],[0]],[[28072,0],[0]],[[0,0],[0]],[[55968,0],[0]],[[0,0],[0]],[[66616,44],[44]],[[0,0],[0]],[[45936,308],[308]],[[0,0],[0]],[[16632,704],[704]],[[0,0],[0]],[[2376,572],[572]],[[0,0],[0]],[[0,132],[132]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
