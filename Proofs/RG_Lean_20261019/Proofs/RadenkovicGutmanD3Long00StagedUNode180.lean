/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode179
import Proofs.RadenkovicGutmanD3Long00StagedUNode120
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e180 : NestedArithmetic.Expr 3 := .times e179 e120
noncomputable def p180 : NestedHorner.Poly 3 := [[[-1]],[[0]],[[-14]],[[0]],[[-81]],[[0]],[[-250]],[[0]],[[-444]],[[0]],[[-458]],[[0]],[[-265]],[[0]],[[-78]],[[0]],[[-9]]]
theorem step180 : p180=NestedArithmetic.mul p179 p120 := by decide +kernel
#print axioms step180
theorem h180 : NestedArithmetic.compile e180=p180 := StagedExprCompile.compile_times e180 e179 e120 p179 p120 p180 rfl h179 h120 step180
#print axioms h180
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
