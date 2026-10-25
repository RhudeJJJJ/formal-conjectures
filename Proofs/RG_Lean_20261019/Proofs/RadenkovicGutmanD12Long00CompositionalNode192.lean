/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode191
import Proofs.RadenkovicGutmanD12Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[42,0],[0,0]],[[0,0],[0,0]],[[368,0],[0,0]],[[0,0],[0,0]],[[1766,0],[0,0]],[[0,0],[0,0]],[[5100,0],[0,0]],[[0,0],[0,0]],[[9144,2],[2,0]],[[0,0],[0,0]],[[10100,28],[28,0]],[[0,0],[0,0]],[[6502,140],[140,0]],[[0,0],[0,0]],[[2010,312],[312,0]],[[0,0],[0,0]],[[18,306],[306,0]],[[0,0],[0,0]],[[-108,108],[108,2]],[[0],[0,0]],[[0],[0,12]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
