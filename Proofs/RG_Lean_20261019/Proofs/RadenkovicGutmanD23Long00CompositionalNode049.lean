/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode045
import Proofs.RadenkovicGutmanD23Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,23]],[[0,0],[0,0]],[[-207,345],[345,2]],[[0,0],[0]],[[2535,1168],[1168]],[[0,0],[0]],[[21235,1290],[1290]],[[0,0],[0]],[[60180,550],[550]],[[0,0],[0]],[[88060,85],[85]],[[0,0],[0]],[[74652,2],[2]],[[0]],[[37957]],[[0]],[[11448]],[[0]],[[1913]],[[0]],[[145]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
