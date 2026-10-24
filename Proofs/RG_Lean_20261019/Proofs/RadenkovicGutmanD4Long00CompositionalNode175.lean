/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode151
import Proofs.RadenkovicGutmanD4Long00CompositionalNode174
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e175 : NestedArithmetic.Expr 3 := .plus e151 e174
noncomputable def p175 : NestedHorner.Poly 3 := [[[1],[]],[[0,0],[0]],[[17,0],[0,0]],[[0,0],[0,0]],[[122,0],[0,0]],[[0,0],[0,0]],[[481,0],[0,0]],[[0,0],[0,0]],[[1136,0],[0,0]],[[0,0],[0,0]],[[1644,1],[1,0]],[[0,0],[0,0]],[[1430,8],[8,0]],[[0,0],[0,0]],[[697,22],[22,0]],[[0,0],[0,0]],[[159,24],[24,0]],[[0,0],[0,0]],[[9,9],[9,0]],[[],[0,0]],[[],[0,1]]]
theorem step175 : p175=NestedHorner.add p151 p174 := by decide +kernel
#print axioms step175
theorem h175 : NestedArithmetic.compile e175=p175 := StagedExprCompile.compile_plus e175 e151 e174 p151 p174 p175 rfl h151 h174 step175
#print axioms h175
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
