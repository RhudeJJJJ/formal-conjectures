/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode034
import Proofs.RadenkovicGutmanD23Long00CompositionalNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e218 : NestedArithmetic.Expr 3 := .times e034 e183
noncomputable def p218 : NestedHorner.Poly 3 := [[[-23],[0]],[[0,0],[0]],[[-368,0],[0]],[[0,0],[0]],[[-2461,0],[0]],[[0,0],[0]],[[-8924,0],[0]],[[0,0],[0]],[[-19044,0],[0]],[[0,0],[0]],[[-24288,-23],[-23]],[[0,0],[0]],[[-17917,-161],[-161]],[[0,0],[0]],[[-6900,-368],[-368]],[[0,0],[0]],[[-1035,-299],[-299]],[[0,0],[0]],[[0,-69],[-69]]]
theorem step218 : p218=NestedArithmetic.mul p034 p183 := by decide +kernel
#print axioms step218
theorem h218 : NestedArithmetic.compile e218=p218 := StagedExprCompile.compile_times e218 e034 e183 p034 p183 p218 rfl h034 h183 step218
#print axioms h218
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
