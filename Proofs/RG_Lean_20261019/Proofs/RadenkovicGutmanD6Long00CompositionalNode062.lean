/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode044
import Proofs.RadenkovicGutmanD6Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,6]],[[0,0],[0,0]],[[54,54],[54,2]],[[0,0],[0]],[[972,162],[162]],[[0,0],[0]],[[4500,180],[180]],[[0,0],[0]],[[9974,92],[92]],[[0,0],[0]],[[12724,22],[22]],[[0,0],[0]],[[10104,2],[2]],[[0]],[[5158]],[[0]],[[1694]],[[0]],[[346]],[[0]],[[40]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
