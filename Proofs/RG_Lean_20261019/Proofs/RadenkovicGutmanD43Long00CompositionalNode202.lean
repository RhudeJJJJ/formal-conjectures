/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode191
import Proofs.RadenkovicGutmanD43Long00CompositionalNode176
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e202 : NestedArithmetic.Expr 3 := .times e191 e176
noncomputable def p202 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[77,0],[0,0]],[[0,0],[0,0]],[[975,0],[0,0]],[[0,0],[0,0]],[[6208,0],[0,0]],[[0,0],[0,0]],[[22955,0],[0,0]],[[0,0],[0,0]],[[52136,2],[2,0]],[[0,0],[0,0]],[[73552,59],[59,0]],[[0,0],[0,0]],[[62884,388],[388,0]],[[0,0],[0,0]],[[30289,994],[994,0]],[[0,0],[0,0]],[[6855,1050],[1050,0]],[[0,0],[0,0]],[[387,387],[387,2]],[[0],[0,0]],[[0],[0,43]]]
theorem step202 : p202=NestedArithmetic.mul p191 p176 := by decide +kernel
#print axioms step202
theorem h202 : NestedArithmetic.compile e202=p202 := StagedExprCompile.compile_times e202 e191 e176 p191 p176 p202 rfl h191 h176 step202
#print axioms h202
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
