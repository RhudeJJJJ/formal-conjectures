/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode044
import Proofs.RadenkovicGutmanD29Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,29]],[[0,0],[0,0]],[[261,261],[261,2]],[[0,0],[0]],[[4629,714],[714]],[[0,0],[0]],[[20531,686],[686]],[[0,0],[0]],[[42864,276],[276]],[[0,0],[0]],[[50536,45],[45]],[[0,0],[0]],[[36232,2],[2]],[[0]],[[16221]],[[0]],[[4500]],[[0]],[[737]],[[0]],[[63]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
