/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode030
import Proofs.RadenkovicGutmanD21Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,21]],[[0,0],[0]],[[189,189],[189]],[[0,0],[0]],[[3339,504],[504]],[[0,0],[0]],[[14637,462],[462]],[[0,0],[0]],[[30030,168],[168]],[[0,0],[0]],[[34524,21],[21]],[[0]],[[23856]],[[0]],[[10101]],[[0]],[[2562]],[[0]],[[357]],[[0]],[[21]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
