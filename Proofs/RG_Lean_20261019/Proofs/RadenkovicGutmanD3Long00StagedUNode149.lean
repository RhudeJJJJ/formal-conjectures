/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode146
import Proofs.RadenkovicGutmanD3Long00StagedUNode148
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e149 : NestedArithmetic.Expr 3 := .times e146 e148
noncomputable def p149 : NestedHorner.Poly 3 := [[[1],[]],[[0,0],[0]],[[16,0],[0,0]],[[0,0],[0,0]],[[108,0],[0,0]],[[0,0],[0,0]],[[400,0],[0,0]],[[0,0],[0,0]],[[886,0],[0,0]],[[0,0],[0,0]],[[1200,1],[1,0]],[[0,0],[0,0]],[[972,8],[8,0]],[[0,0],[0,0]],[[432,22],[22,0]],[[0,0],[0,0]],[[81,24],[24,0]],[[0,0],[0,0]],[[0,9],[9,0]],[[],[0,0]],[[],[0,1]]]
theorem step149 : p149=NestedArithmetic.mul p146 p148 := by decide +kernel
#print axioms step149
theorem h149 : NestedArithmetic.compile e149=p149 := StagedExprCompile.compile_times e149 e146 e148 p146 p148 p149 rfl h146 h148 step149
#print axioms h149
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
