/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode054
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e055 : NestedArithmetic.Expr 3 := .scaled (-1) e054
noncomputable def p055 : NestedHorner.Poly 3 := [[],[[]],[[0]],[[-9]],[[0]],[[-78]],[[0]],[[-265]],[[0]],[[-458]],[[0]],[[-444]],[[0]],[[-250]],[[0]],[[-81]],[[0]],[[-14]],[[0]],[[-1]]]
theorem step055 : p055=NestedHorner.scale (-1) p054 := by decide +kernel
#print axioms step055
theorem h055 : NestedArithmetic.compile e055=p055 := StagedExprCompile.compile_scaled (-1) e055 e054 p054 p055 rfl h054 step055
#print axioms h055
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
