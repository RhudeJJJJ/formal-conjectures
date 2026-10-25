/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode034
import Proofs.RadenkovicGutmanD24Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-48],[0]],[[0,0],[0]],[[-720,0],[0]],[[0,0],[0]],[[-4512,0],[0]],[[0,0],[0]],[[-15312,0],[0]],[[0,0],[0]],[[-30528,0],[0]],[[0,0],[0]],[[-36336,-24],[-24]],[[0,0],[0]],[[-25056,-168],[-168]],[[0,0],[0]],[[-9072,-384],[-384]],[[0,0],[0]],[[-1296,-312],[-312]],[[0,0],[0]],[[0,-72],[-72]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
