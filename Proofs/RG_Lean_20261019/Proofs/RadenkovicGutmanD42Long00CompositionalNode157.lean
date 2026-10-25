/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode156
import Proofs.RadenkovicGutmanD42Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e157 : NestedArithmetic.Expr 3 := .times e156 e003
noncomputable def p157 : NestedHorner.Poly 3 := [[[]],[[0]],[[-1]],[[0]],[[-14]],[[0]],[[-81]],[[0]],[[-250]],[[0]],[[-444]],[[0]],[[-458]],[[0]],[[-265]],[[0]],[[-78]],[[0]],[[-9]]]
theorem step157 : p157=NestedArithmetic.mul p156 p003 := by decide +kernel
#print axioms step157
theorem h157 : NestedArithmetic.compile e157=p157 := StagedExprCompile.compile_times e157 e156 e003 p156 p003 p157 rfl h156 h003 step157
#print axioms h157
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
