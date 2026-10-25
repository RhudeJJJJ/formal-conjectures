/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode030
import Proofs.RadenkovicGutmanD36Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,36]],[[0,0],[0]],[[324,324],[324]],[[0,0],[0]],[[5724,864],[864]],[[0,0],[0]],[[25092,792],[792]],[[0,0],[0]],[[51480,288],[288]],[[0,0],[0]],[[59184,36],[36]],[[0]],[[40896]],[[0]],[[17316]],[[0]],[[4392]],[[0]],[[612]],[[0]],[[36]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
