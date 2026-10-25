/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode030
import Proofs.RadenkovicGutmanD24Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e053 : NestedArithmetic.Expr 3 := .times e030 e052
noncomputable def p053 : NestedHorner.Poly 3 := [[[0],[0,24]],[[0,0],[0]],[[216,216],[216]],[[0,0],[0]],[[3816,576],[576]],[[0,0],[0]],[[16728,528],[528]],[[0,0],[0]],[[34320,192],[192]],[[0,0],[0]],[[39456,24],[24]],[[0]],[[27264]],[[0]],[[11544]],[[0]],[[2928]],[[0]],[[408]],[[0]],[[24]]]
theorem step053 : p053=NestedArithmetic.mul p030 p052 := by decide +kernel
#print axioms step053
theorem h053 : NestedArithmetic.compile e053=p053 := StagedExprCompile.compile_times e053 e030 e052 p030 p052 p053 rfl h030 h052 step053
#print axioms h053
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
