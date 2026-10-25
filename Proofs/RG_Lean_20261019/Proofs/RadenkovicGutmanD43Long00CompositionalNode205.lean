/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode204
import Proofs.RadenkovicGutmanD43Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[86,0],[0]],[[0,0],[0]],[[1376,0],[0]],[[0,0],[0]],[[9202,0],[0]],[[0,0],[0]],[[33368,0],[0]],[[0,0],[0]],[[71208,0],[0]],[[0,0],[0]],[[90816,86],[86]],[[0,0],[0]],[[66994,602],[602]],[[0,0],[0]],[[25800,1376],[1376]],[[0,0],[0]],[[3870,1118],[1118]],[[0,0],[0]],[[0,258],[258]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
