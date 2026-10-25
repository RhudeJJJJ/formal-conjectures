/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode202
import Proofs.RadenkovicGutmanD6Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[40,0],[0,0]],[[0,0],[0,0]],[[346,0],[0,0]],[[0,0],[0,0]],[[1694,0],[0,0]],[[0,0],[0,0]],[[5158,0],[0,0]],[[0,0],[0,0]],[[10104,2],[2,0]],[[0,0],[0,0]],[[12724,22],[22,0]],[[0,0],[0,0]],[[9974,92],[92,0]],[[0,0],[0,0]],[[4500,180],[180,0]],[[0,0],[0,0]],[[972,162],[162,0]],[[0,0],[0,0]],[[54,54],[54,2]],[[0],[0,0]],[[0],[0,6]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
