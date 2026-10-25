/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode029
import Proofs.RadenkovicGutmanD13Long00CompositionalNode014
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e052 : NestedArithmetic.Expr 3 := .plus e029 e014
noncomputable def p052 : NestedHorner.Poly 3 := [[[],[0,1]],[[0,0],[0]],[[9,9],[9]],[[0,0],[0]],[[159,24],[24]],[[0,0],[0]],[[697,22],[22]],[[0,0],[0]],[[1430,8],[8]],[[0,0],[0]],[[1644,1],[1]],[[0]],[[1136]],[[0]],[[481]],[[0]],[[122]],[[0]],[[17]],[[0]],[[1]]]
theorem step052 : p052=NestedHorner.add p029 p014 := by decide +kernel
#print axioms step052
theorem h052 : NestedArithmetic.compile e052=p052 := StagedExprCompile.compile_plus e052 e029 e014 p029 p014 p052 rfl h029 h014 step052
#print axioms h052
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
