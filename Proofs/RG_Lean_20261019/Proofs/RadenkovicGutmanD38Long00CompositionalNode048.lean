/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode047
import Proofs.RadenkovicGutmanD38Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e048 : NestedArithmetic.Expr 3 := .times e047 e028
noncomputable def p048 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[0,228],[228]],[[0,0],[0]],[[4104,988],[988]],[[0,0],[0]],[[28728,1216],[1216]],[[0,0],[0]],[[79344,532],[532]],[[0,0],[0]],[[115064,76],[76]],[[0]],[[96672]],[[0]],[[48488]],[[0]],[[14288]],[[0]],[[2280]],[[0]],[[152]]]
theorem step048 : p048=NestedArithmetic.mul p047 p028 := by decide +kernel
#print axioms step048
theorem h048 : NestedArithmetic.compile e048=p048 := StagedExprCompile.compile_times e048 e047 e028 p047 p028 p048 rfl h047 h028 step048
#print axioms h048
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
