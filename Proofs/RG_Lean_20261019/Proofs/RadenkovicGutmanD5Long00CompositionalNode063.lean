/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode047
import Proofs.RadenkovicGutmanD5Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e063 : NestedArithmetic.Expr 3 := .times e047 e056
noncomputable def p063 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[0,30],[30]],[[0,0],[0]],[[450,130],[130]],[[0,0],[0]],[[3000,160],[160]],[[0,0],[0]],[[7790,70],[70]],[[0,0],[0]],[[10560,10],[10]],[[0]],[[8280]],[[0]],[[3880]],[[0]],[[1070]],[[0]],[[160]],[[0]],[[10]]]
theorem step063 : p063=NestedArithmetic.mul p047 p056 := by decide +kernel
#print axioms step063
theorem h063 : NestedArithmetic.compile e063=p063 := StagedExprCompile.compile_times e063 e047 e056 p047 p056 p063 rfl h047 h056 step063
#print axioms h063
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
