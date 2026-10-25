/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode047
import Proofs.RadenkovicGutmanD43Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e063 : NestedArithmetic.Expr 3 := .times e047 e056
noncomputable def p063 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[0,258],[258]],[[0,0],[0]],[[3870,1118],[1118]],[[0,0],[0]],[[25800,1376],[1376]],[[0,0],[0]],[[66994,602],[602]],[[0,0],[0]],[[90816,86],[86]],[[0]],[[71208]],[[0]],[[33368]],[[0]],[[9202]],[[0]],[[1376]],[[0]],[[86]]]
theorem step063 : p063=NestedArithmetic.mul p047 p056 := by decide +kernel
#print axioms step063
theorem h063 : NestedArithmetic.compile e063=p063 := StagedExprCompile.compile_times e063 e047 e056 p047 p056 p063 rfl h047 h056 step063
#print axioms h063
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
