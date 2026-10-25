/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode044
import Proofs.RadenkovicGutmanD15Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,15]],[[0,0],[0,0]],[[-135,135],[135,2]],[[0,0],[0]],[[27,378],[378]],[[0,0],[0]],[[2511,378],[378]],[[0,0],[0]],[[8044,164],[164]],[[0,0],[0]],[[12368,31],[31]],[[0,0],[0]],[[11052,2],[2]],[[0]],[[6057]],[[0]],[[2048]],[[0]],[[413]],[[0]],[[45]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
