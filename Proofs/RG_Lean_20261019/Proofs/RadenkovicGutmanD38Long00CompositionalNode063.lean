/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode047
import Proofs.RadenkovicGutmanD38Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e063 : NestedArithmetic.Expr 3 := .times e047 e056
noncomputable def p063 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[0,228],[228]],[[0,0],[0]],[[3420,988],[988]],[[0,0],[0]],[[22800,1216],[1216]],[[0,0],[0]],[[59204,532],[532]],[[0,0],[0]],[[80256,76],[76]],[[0]],[[62928]],[[0]],[[29488]],[[0]],[[8132]],[[0]],[[1216]],[[0]],[[76]]]
theorem step063 : p063=NestedArithmetic.mul p047 p056 := by decide +kernel
#print axioms step063
theorem h063 : NestedArithmetic.compile e063=p063 := StagedExprCompile.compile_times e063 e047 e056 p047 p056 p063 rfl h047 h056 step063
#print axioms h063
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
