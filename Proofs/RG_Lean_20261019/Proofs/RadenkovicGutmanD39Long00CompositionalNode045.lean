/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode044
import Proofs.RadenkovicGutmanD39Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,39]],[[0,0],[0,0]],[[-351,351],[351,2]],[[0,0],[0]],[[99,954],[954]],[[0,0],[0]],[[6519,906],[906]],[[0,0],[0]],[[20380,356],[356]],[[0,0],[0]],[[30512,55],[55]],[[0,0],[0]],[[26316,2],[2]],[[0]],[[13713]],[[0]],[[4304]],[[0]],[[773]],[[0]],[[69]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
