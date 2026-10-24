/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode172
import Proofs.RadenkovicGutmanD3Long00StagedUNode174
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e175 : NestedArithmetic.Expr 3 := .times e172 e174
noncomputable def p175 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-34,0],[0,0]],[[0,0],[0,0]],[[-244,0],[0,0]],[[0,0],[0,0]],[[-962,0],[0,0]],[[0,0],[0,0]],[[-2272,0],[0,0]],[[0,0],[0,0]],[[-3288,-2],[-2,0]],[[0,0],[0,0]],[[-2860,-16],[-16,0]],[[0,0],[0,0]],[[-1394,-44],[-44,0]],[[0,0],[0,0]],[[-318,-48],[-48,0]],[[0,0],[0,0]],[[-18,-18],[-18,0]],[[0],[0,0]],[[0],[0,-2]]]
theorem step175 : p175=NestedArithmetic.mul p172 p174 := by decide +kernel
#print axioms step175
theorem h175 : NestedArithmetic.compile e175=p175 := StagedExprCompile.compile_times e175 e172 e174 p172 p174 p175 rfl h172 h174 step175
#print axioms h175
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
