/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode180
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e181 : NestedArithmetic.Expr 3 := .scaled (-1) e180
noncomputable def p181 : NestedHorner.Poly 3 := [[[-1]],[[0]],[[-14]],[[0]],[[-81]],[[0]],[[-250]],[[0]],[[-444]],[[0]],[[-458]],[[0]],[[-265]],[[0]],[[-78]],[[0]],[[-9]]]
theorem step181 : p181=NestedHorner.scale (-1) p180 := by decide +kernel
#print axioms step181
theorem h181 : NestedArithmetic.compile e181=p181 := StagedExprCompile.compile_scaled (-1) e181 e180 p180 p181 rfl h180 step181
#print axioms h181
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
