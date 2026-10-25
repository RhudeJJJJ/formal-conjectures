/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode045
import Proofs.RadenkovicGutmanD40Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,40]],[[0,0],[0,0]],[[-360,600],[600,2]],[[0,0],[0]],[[4422,2018],[2018]],[[0,0],[0]],[[36926,2208],[2208]],[[0,0],[0]],[[104414,924],[924]],[[0,0],[0]],[[152388,136],[136]],[[0,0],[0]],[[128712,2],[2]],[[0]],[[65072]],[[0]],[[19438]],[[0]],[[3188]],[[0]],[[230]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
