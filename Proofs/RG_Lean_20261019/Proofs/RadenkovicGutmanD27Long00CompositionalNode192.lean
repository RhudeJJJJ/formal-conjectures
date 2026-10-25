/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode191
import Proofs.RadenkovicGutmanD27Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[57,0],[0,0]],[[0,0],[0,0]],[[593,0],[0,0]],[[0,0],[0,0]],[[3176,0],[0,0]],[[0,0],[0,0]],[[9885,0],[0,0]],[[0,0],[0,0]],[[18684,2],[2,0]],[[0,0],[0,0]],[[21440,43],[43,0]],[[0,0],[0,0]],[[14212,260],[260,0]],[[0,0],[0,0]],[[4515,642],[642,0]],[[0,0],[0,0]],[[63,666],[666,0]],[[0,0],[0,0]],[[-243,243],[243,2]],[[0],[0,0]],[[0],[0,27]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
