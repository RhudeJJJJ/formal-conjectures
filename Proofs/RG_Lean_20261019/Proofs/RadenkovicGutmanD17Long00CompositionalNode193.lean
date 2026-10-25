/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode192
import Proofs.RadenkovicGutmanD17Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[47,0],[0,0]],[[0,0],[0,0]],[[443,0],[0,0]],[[0,0],[0,0]],[[2236,0],[0,0]],[[0,0],[0,0]],[[6695,0],[0,0]],[[0,0],[0,0]],[[12324,2],[2,0]],[[0,0],[0,0]],[[13880,33],[33,0]],[[0,0],[0,0]],[[9072,180],[180,0]],[[0,0],[0,0]],[[2845,422],[422,0]],[[0,0],[0,0]],[[33,426],[426,0]],[[0,0],[0,0]],[[-153,153],[153,2]],[[0],[0,0]],[[0],[0,17]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
