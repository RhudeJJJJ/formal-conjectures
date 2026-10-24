/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode045
import Proofs.RadenkovicGutmanD2Long00CompositionalNode054
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .times e045 e054
noncomputable def p061 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[0,12],[12]],[[0,0],[0]],[[180,52],[52]],[[0,0],[0]],[[1200,64],[64]],[[0,0],[0]],[[3116,28],[28]],[[0,0],[0]],[[4224,4],[4]],[[0]],[[3312]],[[0]],[[1552]],[[0]],[[428]],[[0]],[[64]],[[0]],[[4]]]
theorem step061 : p061=NestedArithmetic.mul p045 p054 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_times e061 e045 e054 p045 p054 p061 rfl h045 h054 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
