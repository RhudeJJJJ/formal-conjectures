/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode034
import Proofs.RadenkovicGutmanD40Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-40],[0]],[[0,0],[0]],[[-640,0],[0]],[[0,0],[0]],[[-4280,0],[0]],[[0,0],[0]],[[-15520,0],[0]],[[0,0],[0]],[[-33120,0],[0]],[[0,0],[0]],[[-42240,-40],[-40]],[[0,0],[0]],[[-31160,-280],[-280]],[[0,0],[0]],[[-12000,-640],[-640]],[[0,0],[0]],[[-1800,-520],[-520]],[[0,0],[0]],[[0,-120],[-120]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
