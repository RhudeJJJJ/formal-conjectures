/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode034
import Proofs.RadenkovicGutmanD36Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-72],[0]],[[0,0],[0]],[[-1080,0],[0]],[[0,0],[0]],[[-6768,0],[0]],[[0,0],[0]],[[-22968,0],[0]],[[0,0],[0]],[[-45792,0],[0]],[[0,0],[0]],[[-54504,-36],[-36]],[[0,0],[0]],[[-37584,-252],[-252]],[[0,0],[0]],[[-13608,-576],[-576]],[[0,0],[0]],[[-1944,-468],[-468]],[[0,0],[0]],[[0,-108],[-108]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
