/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode191
import Proofs.RadenkovicGutmanD17Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[51,0],[0,0]],[[0,0],[0,0]],[[533,0],[0,0]],[[0,0],[0,0]],[[3036,0],[0,0]],[[0,0],[0,0]],[[10449,0],[0,0]],[[0,0],[0,0]],[[22600,2],[2,0]],[[0,0],[0,0]],[[30808,33],[33,0]],[[0,0],[0,0]],[[25704,180],[180,0]],[[0,0],[0,0]],[[12167,422],[422,0]],[[0,0],[0,0]],[[2721,426],[426,0]],[[0,0],[0,0]],[[153,153],[153,2]],[[0],[0,0]],[[0],[0,17]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
