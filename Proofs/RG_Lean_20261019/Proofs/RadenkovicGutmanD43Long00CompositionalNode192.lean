/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode191
import Proofs.RadenkovicGutmanD43Long00CompositionalNode158
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e192 : NestedArithmetic.Expr 3 := .times e191 e158
noncomputable def p192 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[73,0],[0,0]],[[0,0],[0,0]],[[833,0],[0,0]],[[0,0],[0,0]],[[4680,0],[0,0]],[[0,0],[0,0]],[[14989,0],[0,0]],[[0,0],[0,0]],[[28860,2],[2,0]],[[0,0],[0,0]],[[33536,59],[59,0]],[[0,0],[0,0]],[[22436,388],[388,0]],[[0,0],[0,0]],[[7187,994],[994,0]],[[0,0],[0,0]],[[111,1050],[1050,0]],[[0,0],[0,0]],[[-387,387],[387,2]],[[0],[0,0]],[[0],[0,43]]]
theorem step192 : p192=NestedArithmetic.mul p191 p158 := by decide +kernel
#print axioms step192
theorem h192 : NestedArithmetic.compile e192=p192 := StagedExprCompile.compile_times e192 e191 e158 p191 p158 p192 rfl h191 h158 step192
#print axioms h192
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
