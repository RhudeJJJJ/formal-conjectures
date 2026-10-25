/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode044
import Proofs.RadenkovicGutmanD21Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,21]],[[0,0],[0,0]],[[-189,189],[189,2]],[[0,0],[0]],[[45,522],[522]],[[0,0],[0]],[[3513,510],[510]],[[0,0],[0]],[[11128,212],[212]],[[0,0],[0]],[[16904,37],[37]],[[0,0],[0]],[[14868,2],[2]],[[0]],[[7971]],[[0]],[[2612]],[[0]],[[503]],[[0]],[[51]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
