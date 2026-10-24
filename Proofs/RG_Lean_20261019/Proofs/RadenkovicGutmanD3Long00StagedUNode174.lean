/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode150
import Proofs.RadenkovicGutmanD3Long00StagedUNode173
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e174 : NestedArithmetic.Expr 3 := .plus e150 e173
noncomputable def p174 : NestedHorner.Poly 3 := [[[1],[]],[[0,0],[0]],[[17,0],[0,0]],[[0,0],[0,0]],[[122,0],[0,0]],[[0,0],[0,0]],[[481,0],[0,0]],[[0,0],[0,0]],[[1136,0],[0,0]],[[0,0],[0,0]],[[1644,1],[1,0]],[[0,0],[0,0]],[[1430,8],[8,0]],[[0,0],[0,0]],[[697,22],[22,0]],[[0,0],[0,0]],[[159,24],[24,0]],[[0,0],[0,0]],[[9,9],[9,0]],[[],[0,0]],[[],[0,1]]]
theorem step174 : p174=NestedHorner.add p150 p173 := by decide +kernel
#print axioms step174
theorem h174 : NestedArithmetic.compile e174=p174 := StagedExprCompile.compile_plus e174 e150 e173 p150 p173 p174 rfl h150 h173 step174
#print axioms h174
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
