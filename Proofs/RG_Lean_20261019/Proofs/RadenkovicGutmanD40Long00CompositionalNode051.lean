/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode049
import Proofs.RadenkovicGutmanD40Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,40]],[[0,0],[0,0]],[[-360,600],[600,2]],[[0,0],[0]],[[4458,2018],[2018]],[[0,0],[0]],[[37238,2208],[2208]],[[0,0],[0]],[[105474,924],[924]],[[0,0],[0]],[[154220,136],[136]],[[0,0],[0]],[[130488,2],[2]],[[0]],[[66072]],[[0]],[[19762]],[[0]],[[3244]],[[0]],[[234]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
