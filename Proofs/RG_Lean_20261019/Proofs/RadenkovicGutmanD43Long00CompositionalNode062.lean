/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode044
import Proofs.RadenkovicGutmanD43Long00CompositionalNode052
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e062 : NestedArithmetic.Expr 3 := .times e044 e052
noncomputable def p062 : NestedHorner.Poly 3 := [[[0],[0,43]],[[0,0],[0,0]],[[387,387],[387,2]],[[0,0],[0]],[[6855,1050],[1050]],[[0,0],[0]],[[30289,994],[994]],[[0,0],[0]],[[62884,388],[388]],[[0,0],[0]],[[73552,59],[59]],[[0,0],[0]],[[52136,2],[2]],[[0]],[[22955]],[[0]],[[6208]],[[0]],[[975]],[[0]],[[77]],[[0]],[[2]]]
theorem step062 : p062=NestedArithmetic.mul p044 p052 := by decide +kernel
#print axioms step062
theorem h062 : NestedArithmetic.compile e062=p062 := StagedExprCompile.compile_times e062 e044 e052 p044 p052 p062 rfl h044 h052 step062
#print axioms h062
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
