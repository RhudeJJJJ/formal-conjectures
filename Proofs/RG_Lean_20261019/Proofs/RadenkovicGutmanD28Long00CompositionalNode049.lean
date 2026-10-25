/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode045
import Proofs.RadenkovicGutmanD28Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,28]],[[0,0],[0,0]],[[-252,420],[420,2]],[[0,0],[0]],[[3090,1418],[1418]],[[0,0],[0]],[[25850,1560],[1560]],[[0,0],[0]],[[73190,660],[660]],[[0,0],[0]],[[106980,100],[100]],[[0,0],[0]],[[90552,2],[2]],[[0]],[[45932]],[[0]],[[13798]],[[0]],[[2288]],[[0]],[[170]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
