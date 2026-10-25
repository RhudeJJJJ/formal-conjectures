/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode030
import Proofs.RadenkovicGutmanD30Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,30]],[[0,0],[0]],[[270,270],[270]],[[0,0],[0]],[[4770,720],[720]],[[0,0],[0]],[[20910,660],[660]],[[0,0],[0]],[[42900,240],[240]],[[0,0],[0]],[[49320,30],[30]],[[0]],[[34080]],[[0]],[[14430]],[[0]],[[3660]],[[0]],[[510]],[[0]],[[30]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
