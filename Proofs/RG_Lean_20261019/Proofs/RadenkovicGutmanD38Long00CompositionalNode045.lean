/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode044
import Proofs.RadenkovicGutmanD38Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,38]],[[0,0],[0,0]],[[-342,342],[342,2]],[[0,0],[0]],[[96,930],[930]],[[0,0],[0]],[[6352,884],[884]],[[0,0],[0]],[[19866,348],[348]],[[0,0],[0]],[[29756,54],[54]],[[0,0],[0]],[[25680,2],[2]],[[0]],[[13394]],[[0]],[[4210]],[[0]],[[758]],[[0]],[[68]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
