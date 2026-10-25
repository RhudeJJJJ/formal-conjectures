/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode059
import Proofs.RadenkovicGutmanD39Long00CompositionalNode060
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e061 : NestedArithmetic.Expr 3 := .plus e059 e060
noncomputable def p061 : NestedHorner.Poly 3 := [[[0],[0]],[[0,117],[117,-74]],[[0,0],[0]],[[1089,-159],[-159]],[[0,0],[0]],[[-66,-1152],[-1152]],[[0,0],[0]],[[-21197,-1355],[-1355]],[[0,0],[0]],[[-64636,-553],[-553]],[[0,0],[0]],[[-89364,-74],[-74]],[[0]],[[-68932]],[[0]],[[-31421]],[[0]],[[-8404]],[[0]],[[-1219]],[[0]],[[-74]]]
theorem step061 : p061=NestedHorner.add p059 p060 := by decide +kernel
#print axioms step061
theorem h061 : NestedArithmetic.compile e061=p061 := StagedExprCompile.compile_plus e061 e059 e060 p059 p060 p061 rfl h059 h060 step061
#print axioms h061
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
