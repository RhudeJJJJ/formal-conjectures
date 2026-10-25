/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode192
import Proofs.RadenkovicGutmanD21Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[51,0],[0,0]],[[0,0],[0,0]],[[503,0],[0,0]],[[0,0],[0,0]],[[2612,0],[0,0]],[[0,0],[0,0]],[[7971,0],[0,0]],[[0,0],[0,0]],[[14868,2],[2,0]],[[0,0],[0,0]],[[16904,37],[37,0]],[[0,0],[0,0]],[[11128,212],[212,0]],[[0,0],[0,0]],[[3513,510],[510,0]],[[0,0],[0,0]],[[45,522],[522,0]],[[0,0],[0,0]],[[-189,189],[189,2]],[[0],[0,0]],[[0],[0,21]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
