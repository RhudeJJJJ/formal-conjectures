/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode030
import Proofs.RadenkovicGutmanD37Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,37]],[[0,0],[0]],[[333,333],[333]],[[0,0],[0]],[[5883,888],[888]],[[0,0],[0]],[[25789,814],[814]],[[0,0],[0]],[[52910,296],[296]],[[0,0],[0]],[[60828,37],[37]],[[0]],[[42032]],[[0]],[[17797]],[[0]],[[4514]],[[0]],[[629]],[[0]],[[37]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
