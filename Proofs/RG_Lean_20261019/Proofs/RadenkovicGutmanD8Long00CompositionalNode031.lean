/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode014
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e031 : NestedArithmetic.Expr 3 := .scaled (-1) e014
noncomputable def p031 : NestedHorner.Poly 3 := [[],[[]],[[-9]],[[0]],[[-78]],[[0]],[[-265]],[[0]],[[-458]],[[0]],[[-444]],[[0]],[[-250]],[[0]],[[-81]],[[0]],[[-14]],[[0]],[[-1]]]
theorem step031 : p031=NestedHorner.scale (-1) p014 := by decide +kernel
#print axioms step031
theorem h031 : NestedArithmetic.compile e031=p031 := StagedExprCompile.compile_scaled (-1) e031 e014 p014 p031 rfl h014 step031
#print axioms h031
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
