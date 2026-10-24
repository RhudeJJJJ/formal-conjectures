/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode192
import Proofs.RadenkovicGutmanD5Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[35,0],[0,0]],[[0,0],[0,0]],[[263,0],[0,0]],[[0,0],[0,0]],[[1108,0],[0,0]],[[0,0],[0,0]],[[2867,0],[0,0]],[[0,0],[0,0]],[[4692,2],[2,0]],[[0,0],[0,0]],[[4808,21],[21,0]],[[0,0],[0,0]],[[2904,84],[84,0]],[[0,0],[0,0]],[[841,158],[158,0]],[[0,0],[0,0]],[[-3,138],[138,0]],[[0,0],[0,0]],[[-45,45],[45,2]],[[0],[0,0]],[[0],[0,5]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
