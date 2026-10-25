/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode030
import Proofs.RadenkovicGutmanD12Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,12]],[[0,0],[0]],[[108,108],[108]],[[0,0],[0]],[[1908,288],[288]],[[0,0],[0]],[[8364,264],[264]],[[0,0],[0]],[[17160,96],[96]],[[0,0],[0]],[[19728,12],[12]],[[0]],[[13632]],[[0]],[[5772]],[[0]],[[1464]],[[0]],[[204]],[[0]],[[12]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
