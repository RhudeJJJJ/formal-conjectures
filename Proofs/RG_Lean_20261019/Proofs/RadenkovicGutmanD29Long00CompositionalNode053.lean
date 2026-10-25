/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode030
import Proofs.RadenkovicGutmanD29Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,29]],[[0,0],[0]],[[261,261],[261]],[[0,0],[0]],[[4611,696],[696]],[[0,0],[0]],[[20213,638],[638]],[[0,0],[0]],[[41470,232],[232]],[[0,0],[0]],[[47676,29],[29]],[[0]],[[32944]],[[0]],[[13949]],[[0]],[[3538]],[[0]],[[493]],[[0]],[[29]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
