/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode157
import Proofs.RadenkovicGutmanD3Long00StagedUNode120
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e158 : NestedArithmetic.Expr 3 := .times e157 e120
noncomputable def p158 : NestedHorner.Poly 3 := [[[-1],[0]],[[0,0],[0]],[[-15,0],[0,0]],[[0,0],[0,0]],[[-94,0],[0,0]],[[0,0],[0,0]],[[-319,0],[0,0]],[[0,0],[0,0]],[[-636,0],[0,0]],[[0,0],[0,0]],[[-756,-1],[-1,0]],[[0,0],[0,0]],[[-514,-8],[-8,0]],[[0,0],[0,0]],[[-167,-22],[-22,0]],[[0,0],[0,0]],[[-3,-24],[-24,0]],[[0,0],[0,0]],[[9,-9],[-9,0]],[[0],[0,0]],[[0],[0,-1]]]
theorem step158 : p158=NestedArithmetic.mul p157 p120 := by decide +kernel
#print axioms step158
theorem h158 : NestedArithmetic.compile e158=p158 := StagedExprCompile.compile_times e158 e157 e120 p157 p120 p158 rfl h157 h120 step158
#print axioms h158
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
