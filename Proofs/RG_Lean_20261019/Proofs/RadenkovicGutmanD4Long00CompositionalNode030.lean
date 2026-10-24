/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode014
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e030 : NestedArithmetic.Expr 3 := .scaled (-1) e014
noncomputable def p030 : NestedHorner.Poly 3 := [[],[[]],[[-9]],[[0]],[[-78]],[[0]],[[-265]],[[0]],[[-458]],[[0]],[[-444]],[[0]],[[-250]],[[0]],[[-81]],[[0]],[[-14]],[[0]],[[-1]]]
theorem step030 : p030=NestedHorner.scale (-1) p014 := by decide +kernel
#print axioms step030
theorem h030 : NestedArithmetic.compile e030=p030 := StagedExprCompile.compile_scaled (-1) e030 e014 p014 p030 rfl h014 step030
#print axioms h030
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
