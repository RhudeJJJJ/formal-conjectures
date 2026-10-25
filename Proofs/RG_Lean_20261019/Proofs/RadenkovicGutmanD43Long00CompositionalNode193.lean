/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode192
import Proofs.RadenkovicGutmanD43Long00CompositionalNode122
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e193 : NestedArithmetic.Expr 3 := .times e192 e122
noncomputable def p193 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[73,0],[0,0]],[[0,0],[0,0]],[[833,0],[0,0]],[[0,0],[0,0]],[[4680,0],[0,0]],[[0,0],[0,0]],[[14989,0],[0,0]],[[0,0],[0,0]],[[28860,2],[2,0]],[[0,0],[0,0]],[[33536,59],[59,0]],[[0,0],[0,0]],[[22436,388],[388,0]],[[0,0],[0,0]],[[7187,994],[994,0]],[[0,0],[0,0]],[[111,1050],[1050,0]],[[0,0],[0,0]],[[-387,387],[387,2]],[[0],[0,0]],[[0],[0,43]]]
theorem step193 : p193=NestedArithmetic.mul p192 p122 := by decide +kernel
#print axioms step193
theorem h193 : NestedArithmetic.compile e193=p193 := StagedExprCompile.compile_times e193 e192 e122 p192 p122 p193 rfl h192 h122 step193
#print axioms h193
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
