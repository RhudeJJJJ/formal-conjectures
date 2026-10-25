/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode044
import Proofs.RadenkovicGutmanD37Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,37]],[[0,0],[0,0]],[[333,333],[333,2]],[[0,0],[0]],[[5901,906],[906]],[[0,0],[0]],[[26107,862],[862]],[[0,0],[0]],[[54304,340],[340]],[[0,0],[0]],[[63688,53],[53]],[[0,0],[0]],[[45320,2],[2]],[[0]],[[20069]],[[0]],[[5476]],[[0]],[[873]],[[0]],[[71]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
