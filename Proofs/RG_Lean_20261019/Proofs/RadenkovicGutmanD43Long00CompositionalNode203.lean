/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode202
import Proofs.RadenkovicGutmanD43Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e203 : NestedArithmetic.Expr 3 := .times e202 e122
noncomputable def p203 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[77,0],[0,0]],[[0,0],[0,0]],[[975,0],[0,0]],[[0,0],[0,0]],[[6208,0],[0,0]],[[0,0],[0,0]],[[22955,0],[0,0]],[[0,0],[0,0]],[[52136,2],[2,0]],[[0,0],[0,0]],[[73552,59],[59,0]],[[0,0],[0,0]],[[62884,388],[388,0]],[[0,0],[0,0]],[[30289,994],[994,0]],[[0,0],[0,0]],[[6855,1050],[1050,0]],[[0,0],[0,0]],[[387,387],[387,2]],[[0],[0,0]],[[0],[0,43]]]
theorem step203 : p203=NestedArithmetic.mul p202 p122 := by decide +kernel
#print axioms step203
theorem h203 : NestedArithmetic.compile e203=p203 := StagedExprCompile.compile_times e203 e202 e122 p202 p122 p203 rfl h202 h122 step203
#print axioms h203
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
