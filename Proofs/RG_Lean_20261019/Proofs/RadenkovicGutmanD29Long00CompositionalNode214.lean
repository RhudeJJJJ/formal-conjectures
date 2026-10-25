/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode030
import Proofs.RadenkovicGutmanD29Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e214 : NestedArithmetic.Expr 3 := .times e030 e176
noncomputable def p214 : NestedHorner.Poly 3 := [[[29],[0]],[[0,0],[0]],[[493,0],[0,0]],[[0,0],[0,0]],[[3538,0],[0,0]],[[0,0],[0,0]],[[13949,0],[0,0]],[[0,0],[0,0]],[[32944,0],[0,0]],[[0,0],[0,0]],[[47676,29],[29,0]],[[0,0],[0,0]],[[41470,232],[232,0]],[[0,0],[0,0]],[[20213,638],[638,0]],[[0,0],[0,0]],[[4611,696],[696,0]],[[0,0],[0,0]],[[261,261],[261,0]],[[0],[0,0]],[[0],[0,29]]]
theorem step214 : p214=NestedArithmetic.mul p030 p176 := by decide +kernel
#print axioms step214
theorem h214 : NestedArithmetic.compile e214=p214 := StagedExprCompile.compile_times e214 e030 e176 p030 p176 p214 rfl h030 h176 step214
#print axioms h214
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
