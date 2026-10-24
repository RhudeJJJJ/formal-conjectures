/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode158
import Proofs.RadenkovicGutmanD3Long00StagedUNode160
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e161 : NestedArithmetic.Expr 3 := .plus e158 e160
noncomputable def p161 : NestedHorner.Poly 3 := [[[-1],[0]],[[0,0],[0]],[[-11,0],[0,0]],[[0,0],[0,0]],[[-38,0],[0,0]],[[0,0],[0,0]],[[5,0],[0,0]],[[0,0],[0,0]],[[364,0],[0,0]],[[0,0],[0,0]],[[1020,-1],[-1,0]],[[0,0],[0,0]],[[1318,-8],[-8,0]],[[0,0],[0,0]],[[893,-22],[-22,0]],[[0,0],[0,0]],[[309,-24],[-24,0]],[[0,0],[0,0]],[[45,-9],[-9,0]],[[0],[0,0]],[[0],[0,-1]]]
theorem step161 : p161=NestedHorner.add p158 p160 := by decide +kernel
#print axioms step161
theorem h161 : NestedArithmetic.compile e161=p161 := StagedExprCompile.compile_plus e161 e158 e160 p158 p160 p161 rfl h158 h160 step161
#print axioms h161
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
