/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode045
import Proofs.RadenkovicGutmanD10Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,10]],[[0,0],[0,0]],[[-90,150],[150,2]],[[0,0],[0]],[[1092,518],[518]],[[0,0],[0]],[[9236,588],[588]],[[0,0],[0]],[[26354,264],[264]],[[0,0],[0]],[[38868,46],[46]],[[0,0],[0]],[[33312,2],[2]],[[0]],[[17222]],[[0]],[[5338]],[[0]],[[938]],[[0]],[[80]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
