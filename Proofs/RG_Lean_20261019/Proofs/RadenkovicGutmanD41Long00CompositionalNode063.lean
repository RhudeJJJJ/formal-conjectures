/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode047
import Proofs.RadenkovicGutmanD41Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e063 : NestedArithmetic.Expr 3 := .times e047 e056
noncomputable def p063 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[0,246],[246]],[[0,0],[0]],[[3690,1066],[1066]],[[0,0],[0]],[[24600,1312],[1312]],[[0,0],[0]],[[63878,574],[574]],[[0,0],[0]],[[86592,82],[82]],[[0]],[[67896]],[[0]],[[31816]],[[0]],[[8774]],[[0]],[[1312]],[[0]],[[82]]]
theorem step063 : p063=NestedArithmetic.mul p047 p056 := by decide +kernel
#print axioms step063
theorem h063 : NestedArithmetic.compile e063=p063 := StagedExprCompile.compile_times e063 e047 e056 p047 p056 p063 rfl h047 h056 step063
#print axioms h063
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
