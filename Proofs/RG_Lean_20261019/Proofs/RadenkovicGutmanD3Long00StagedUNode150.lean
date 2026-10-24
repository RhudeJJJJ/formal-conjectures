/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode149
import Proofs.RadenkovicGutmanD3Long00StagedUNode120
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e150 : NestedArithmetic.Expr 3 := .times e149 e120
noncomputable def p150 : NestedHorner.Poly 3 := [[[1],[]],[[0,0],[0]],[[16,0],[0,0]],[[0,0],[0,0]],[[108,0],[0,0]],[[0,0],[0,0]],[[400,0],[0,0]],[[0,0],[0,0]],[[886,0],[0,0]],[[0,0],[0,0]],[[1200,1],[1,0]],[[0,0],[0,0]],[[972,8],[8,0]],[[0,0],[0,0]],[[432,22],[22,0]],[[0,0],[0,0]],[[81,24],[24,0]],[[0,0],[0,0]],[[0,9],[9,0]],[[],[0,0]],[[],[0,1]]]
theorem step150 : p150=NestedArithmetic.mul p149 p120 := by decide +kernel
#print axioms step150
theorem h150 : NestedArithmetic.compile e150=p150 := StagedExprCompile.compile_times e150 e149 e120 p149 p120 p150 rfl h149 h120 step150
#print axioms h150
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
