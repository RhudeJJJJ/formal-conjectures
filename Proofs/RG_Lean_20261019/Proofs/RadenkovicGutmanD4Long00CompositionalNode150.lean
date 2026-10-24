/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode147
import Proofs.RadenkovicGutmanD4Long00CompositionalNode149
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e150 : NestedArithmetic.Expr 3 := .times e147 e149
noncomputable def p150 : NestedHorner.Poly 3 := [[[1],[]],[[0,0],[0]],[[16,0],[0,0]],[[0,0],[0,0]],[[108,0],[0,0]],[[0,0],[0,0]],[[400,0],[0,0]],[[0,0],[0,0]],[[886,0],[0,0]],[[0,0],[0,0]],[[1200,1],[1,0]],[[0,0],[0,0]],[[972,8],[8,0]],[[0,0],[0,0]],[[432,22],[22,0]],[[0,0],[0,0]],[[81,24],[24,0]],[[0,0],[0,0]],[[0,9],[9,0]],[[],[0,0]],[[],[0,1]]]
theorem step150 : p150=NestedArithmetic.mul p147 p149 := by decide +kernel
#print axioms step150
theorem h150 : NestedArithmetic.compile e150=p150 := StagedExprCompile.compile_times e150 e147 e149 p147 p149 p150 rfl h147 h149 step150
#print axioms h150
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
