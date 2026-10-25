/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode192
import Proofs.RadenkovicGutmanD42Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[72,0],[0,0]],[[0,0],[0,0]],[[818,0],[0,0]],[[0,0],[0,0]],[[4586,0],[0,0]],[[0,0],[0,0]],[[14670,0],[0,0]],[[0,0],[0,0]],[[28224,2],[2,0]],[[0,0],[0,0]],[[32780,58],[58,0]],[[0,0],[0,0]],[[21922,380],[380,0]],[[0,0],[0,0]],[[7020,972],[972,0]],[[0,0],[0,0]],[[108,1026],[1026,0]],[[0,0],[0,0]],[[-378,378],[378,2]],[[0],[0,0]],[[0],[0,42]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
