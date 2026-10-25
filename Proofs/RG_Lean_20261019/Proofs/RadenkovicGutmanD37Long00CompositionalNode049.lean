/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode045
import Proofs.RadenkovicGutmanD37Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,37]],[[0,0],[0,0]],[[-333,555],[555,2]],[[0,0],[0]],[[4089,1868],[1868]],[[0,0],[0]],[[34157,2046],[2046]],[[0,0],[0]],[[96608,858],[858]],[[0,0],[0]],[[141036,127],[127]],[[0,0],[0]],[[119172,2],[2]],[[0]],[[60287]],[[0]],[[18028]],[[0]],[[2963]],[[0]],[[215]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
