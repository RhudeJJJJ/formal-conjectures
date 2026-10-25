/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode044
import Proofs.RadenkovicGutmanD32Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,32]],[[0,0],[0,0]],[[-288,288],[288,2]],[[0,0],[0]],[[78,786],[786]],[[0,0],[0]],[[5350,752],[752]],[[0,0],[0]],[[16782,300],[300]],[[0,0],[0]],[[25220,48],[48]],[[0,0],[0]],[[21864,2],[2]],[[0]],[[11480]],[[0]],[[3646]],[[0]],[[668]],[[0]],[[62]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
