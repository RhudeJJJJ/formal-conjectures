/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode162
import Proofs.RadenkovicGutmanD3Long00StagedUNode120
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .times e162 e120
noncomputable def p163 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-22,0],[0,0]],[[0,0],[0,0]],[[-76,0],[0,0]],[[0,0],[0,0]],[[10,0],[0,0]],[[0,0],[0,0]],[[728,0],[0,0]],[[0,0],[0,0]],[[2040,-2],[-2,0]],[[0,0],[0,0]],[[2636,-16],[-16,0]],[[0,0],[0,0]],[[1786,-44],[-44,0]],[[0,0],[0,0]],[[618,-48],[-48,0]],[[0,0],[0,0]],[[90,-18],[-18,0]],[[0],[0,0]],[[0],[0,-2]]]
theorem step163 : p163=NestedArithmetic.mul p162 p120 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_times e163 e162 e120 p162 p120 p163 rfl h162 h120 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
