/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode045
import Proofs.RadenkovicGutmanD9Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,9]],[[0,0],[0,0]],[[-81,135],[135,2]],[[0,0],[0]],[[981,468],[468]],[[0,0],[0]],[[8313,534],[534]],[[0,0],[0]],[[23752,242],[242]],[[0,0],[0]],[[35084,43],[43]],[[0,0],[0]],[[30132,2],[2]],[[0]],[[15627]],[[0]],[[4868]],[[0]],[[863]],[[0]],[[75]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
