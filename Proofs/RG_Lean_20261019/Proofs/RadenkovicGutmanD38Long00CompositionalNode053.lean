/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode030
import Proofs.RadenkovicGutmanD38Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,38]],[[0,0],[0]],[[342,342],[342]],[[0,0],[0]],[[6042,912],[912]],[[0,0],[0]],[[26486,836],[836]],[[0,0],[0]],[[54340,304],[304]],[[0,0],[0]],[[62472,38],[38]],[[0]],[[43168]],[[0]],[[18278]],[[0]],[[4636]],[[0]],[[646]],[[0]],[[38]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
