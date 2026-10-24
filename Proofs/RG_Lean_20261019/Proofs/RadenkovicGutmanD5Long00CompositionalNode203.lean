/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode202
import Proofs.RadenkovicGutmanD5Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[39,0],[0,0]],[[0,0],[0,0]],[[329,0],[0,0]],[[0,0],[0,0]],[[1572,0],[0,0]],[[0,0],[0,0]],[[4677,0],[0,0]],[[0,0],[0,0]],[[8968,2],[2,0]],[[0,0],[0,0]],[[11080,21],[21,0]],[[0,0],[0,0]],[[8544,84],[84,0]],[[0,0],[0,0]],[[3803,158],[158,0]],[[0,0],[0,0]],[[813,138],[138,0]],[[0,0],[0,0]],[[45,45],[45,2]],[[0],[0,0]],[[0],[0,5]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
