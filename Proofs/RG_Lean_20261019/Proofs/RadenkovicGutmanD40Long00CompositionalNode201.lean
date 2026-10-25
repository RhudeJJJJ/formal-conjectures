/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode198
import Proofs.RadenkovicGutmanD40Long00CompositionalNode200
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e201 : NestedArithmetic.Expr 3 := .plus e198 e200
noncomputable def p201 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[234,0],[0,0]],[[0,0],[0,0]],[[3244,0],[0,0]],[[0,0],[0,0]],[[19762,0],[0,0]],[[0,0],[0,0]],[[66072,0],[0,0]],[[0,0],[0,0]],[[130488,2],[2,0]],[[0,0],[0,0]],[[154220,136],[136,0]],[[0,0],[0,0]],[[105474,924],[924,0]],[[0,0],[0,0]],[[37238,2208],[2208,0]],[[0,0],[0,0]],[[4458,2018],[2018,0]],[[0,0],[0,0]],[[-360,600],[600,2]],[[0],[0,0]],[[0],[0,40]]]
theorem step201 : p201=NestedHorner.add p198 p200 := by decide +kernel
#print axioms step201
theorem h201 : NestedArithmetic.compile e201=p201 := StagedExprCompile.compile_plus e201 e198 e200 p198 p200 p201 rfl h198 h200 step201
#print axioms h201
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
