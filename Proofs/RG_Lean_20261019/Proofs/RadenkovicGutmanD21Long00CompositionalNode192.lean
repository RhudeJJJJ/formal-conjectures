/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode191
import Proofs.RadenkovicGutmanD21Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[51,0],[0,0]],[[0,0],[0,0]],[[503,0],[0,0]],[[0,0],[0,0]],[[2612,0],[0,0]],[[0,0],[0,0]],[[7971,0],[0,0]],[[0,0],[0,0]],[[14868,2],[2,0]],[[0,0],[0,0]],[[16904,37],[37,0]],[[0,0],[0,0]],[[11128,212],[212,0]],[[0,0],[0,0]],[[3513,510],[510,0]],[[0,0],[0,0]],[[45,522],[522,0]],[[0,0],[0,0]],[[-189,189],[189,2]],[[0],[0,0]],[[0],[0,21]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
