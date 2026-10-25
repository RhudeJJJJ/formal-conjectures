/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode044
import Proofs.RadenkovicGutmanD43Long00CompositionalNode032
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e045 : NestedArithmetic.Expr 3 := .times e044 e032
noncomputable def p045 : NestedHorner.Poly 3 := [[[0],[0,43]],[[0,0],[0,0]],[[-387,387],[387,2]],[[0,0],[0]],[[111,1050],[1050]],[[0,0],[0]],[[7187,994],[994]],[[0,0],[0]],[[22436,388],[388]],[[0,0],[0]],[[33536,59],[59]],[[0,0],[0]],[[28860,2],[2]],[[0]],[[14989]],[[0]],[[4680]],[[0]],[[833]],[[0]],[[73]],[[0]],[[2]]]
theorem step045 : p045=NestedArithmetic.mul p044 p032 := by decide +kernel
#print axioms step045
theorem h045 : NestedArithmetic.compile e045=p045 := StagedExprCompile.compile_times e045 e044 e032 p044 p032 p045 rfl h044 h032 step045
#print axioms h045
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
