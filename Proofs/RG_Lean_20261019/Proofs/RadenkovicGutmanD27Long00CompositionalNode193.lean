/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode192
import Proofs.RadenkovicGutmanD27Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[57,0],[0,0]],[[0,0],[0,0]],[[593,0],[0,0]],[[0,0],[0,0]],[[3176,0],[0,0]],[[0,0],[0,0]],[[9885,0],[0,0]],[[0,0],[0,0]],[[18684,2],[2,0]],[[0,0],[0,0]],[[21440,43],[43,0]],[[0,0],[0,0]],[[14212,260],[260,0]],[[0,0],[0,0]],[[4515,642],[642,0]],[[0,0],[0,0]],[[63,666],[666,0]],[[0,0],[0,0]],[[-243,243],[243,2]],[[0],[0,0]],[[0],[0,27]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
