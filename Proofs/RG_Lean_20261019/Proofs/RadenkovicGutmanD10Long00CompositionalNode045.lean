/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode044
import Proofs.RadenkovicGutmanD10Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,10]],[[0,0],[0,0]],[[-90,90],[90,2]],[[0,0],[0]],[[12,258],[258]],[[0,0],[0]],[[1676,268],[268]],[[0,0],[0]],[[5474,124],[124]],[[0,0],[0]],[[8588,26],[26]],[[0,0],[0]],[[7872,2],[2]],[[0]],[[4462]],[[0]],[[1578]],[[0]],[[338]],[[0]],[[40]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
