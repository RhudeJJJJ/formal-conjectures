/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode117
import Proofs.RadenkovicGutmanD3Long00StagedUNode161
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e162 : NestedArithmetic.Expr 3 := .times e117 e161
noncomputable def p162 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-22,0],[0,0]],[[0,0],[0,0]],[[-76,0],[0,0]],[[0,0],[0,0]],[[10,0],[0,0]],[[0,0],[0,0]],[[728,0],[0,0]],[[0,0],[0,0]],[[2040,-2],[-2,0]],[[0,0],[0,0]],[[2636,-16],[-16,0]],[[0,0],[0,0]],[[1786,-44],[-44,0]],[[0,0],[0,0]],[[618,-48],[-48,0]],[[0,0],[0,0]],[[90,-18],[-18,0]],[[0],[0,0]],[[0],[0,-2]]]
theorem step162 : p162=NestedArithmetic.mul p117 p161 := by decide +kernel
#print axioms step162
theorem h162 : NestedArithmetic.compile e162=p162 := StagedExprCompile.compile_times e162 e117 e161 p117 p161 p162 rfl h117 h161 step162
#print axioms h162
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
