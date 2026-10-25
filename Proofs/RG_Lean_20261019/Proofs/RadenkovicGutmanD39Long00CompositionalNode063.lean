/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode047
import Proofs.RadenkovicGutmanD39Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e063 : NestedArithmetic.Expr 3 := .times e047 e056
noncomputable def p063 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[0,234],[234]],[[0,0],[0]],[[3510,1014],[1014]],[[0,0],[0]],[[23400,1248],[1248]],[[0,0],[0]],[[60762,546],[546]],[[0,0],[0]],[[82368,78],[78]],[[0]],[[64584]],[[0]],[[30264]],[[0]],[[8346]],[[0]],[[1248]],[[0]],[[78]]]
theorem step063 : p063=NestedArithmetic.mul p047 p056 := by decide +kernel
#print axioms step063
theorem h063 : NestedArithmetic.compile e063=p063 := StagedExprCompile.compile_times e063 e047 e056 p047 p056 p063 rfl h047 h056 step063
#print axioms h063
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
