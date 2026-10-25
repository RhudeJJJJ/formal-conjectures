/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode191
import Proofs.RadenkovicGutmanD6Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[40,0],[0,0]],[[0,0],[0,0]],[[346,0],[0,0]],[[0,0],[0,0]],[[1694,0],[0,0]],[[0,0],[0,0]],[[5158,0],[0,0]],[[0,0],[0,0]],[[10104,2],[2,0]],[[0,0],[0,0]],[[12724,22],[22,0]],[[0,0],[0,0]],[[9974,92],[92,0]],[[0,0],[0,0]],[[4500,180],[180,0]],[[0,0],[0,0]],[[972,162],[162,0]],[[0,0],[0,0]],[[54,54],[54,2]],[[0],[0,0]],[[0],[0,6]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
