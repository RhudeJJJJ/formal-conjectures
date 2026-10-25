/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode030
import Proofs.RadenkovicGutmanD6Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,6]],[[0,0],[0]],[[54,54],[54]],[[0,0],[0]],[[954,144],[144]],[[0,0],[0]],[[4182,132],[132]],[[0,0],[0]],[[8580,48],[48]],[[0,0],[0]],[[9864,6],[6]],[[0]],[[6816]],[[0]],[[2886]],[[0]],[[732]],[[0]],[[102]],[[0]],[[6]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
