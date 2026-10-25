/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode202
import Proofs.RadenkovicGutmanD11Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[45,0],[0,0]],[[0,0],[0,0]],[[431,0],[0,0]],[[0,0],[0,0]],[[2304,0],[0,0]],[[0,0],[0,0]],[[7563,0],[0,0]],[[0,0],[0,0]],[[15784,2],[2,0]],[[0,0],[0,0]],[[20944,27],[27,0]],[[0,0],[0,0]],[[17124,132],[132,0]],[[0,0],[0,0]],[[7985,290],[290,0]],[[0,0],[0,0]],[[1767,282],[282,0]],[[0,0],[0,0]],[[99,99],[99,2]],[[0],[0,0]],[[0],[0,11]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
