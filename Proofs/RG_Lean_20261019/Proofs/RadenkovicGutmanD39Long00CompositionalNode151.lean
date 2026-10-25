/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode148
import Proofs.RadenkovicGutmanD39Long00CompositionalNode150
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e151 : NestedArithmetic.Expr 3 := .times e148 e150
noncomputable def p151 : NestedHorner.Poly 3 := [[[1],[]],[[0,0],[0]],[[16,0],[0,0]],[[0,0],[0,0]],[[108,0],[0,0]],[[0,0],[0,0]],[[400,0],[0,0]],[[0,0],[0,0]],[[886,0],[0,0]],[[0,0],[0,0]],[[1200,1],[1,0]],[[0,0],[0,0]],[[972,8],[8,0]],[[0,0],[0,0]],[[432,22],[22,0]],[[0,0],[0,0]],[[81,24],[24,0]],[[0,0],[0,0]],[[0,9],[9,0]],[[],[0,0]],[[],[0,1]]]
theorem step151 : p151=NestedArithmetic.mul p148 p150 := by decide +kernel
#print axioms step151
theorem h151 : NestedArithmetic.compile e151=p151 := StagedExprCompile.compile_times e151 e148 e150 p148 p150 p151 rfl h148 h150 step151
#print axioms h151
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
