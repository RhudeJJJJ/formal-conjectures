/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode045
import Proofs.RadenkovicGutmanD17Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,17]],[[0,0],[0,0]],[[-153,255],[255,2]],[[0,0],[0]],[[1869,868],[868]],[[0,0],[0]],[[15697,966],[966]],[[0,0],[0]],[[44568,418],[418]],[[0,0],[0]],[[65356,67],[67]],[[0,0],[0]],[[55572,2],[2]],[[0]],[[28387]],[[0]],[[8628]],[[0]],[[1463]],[[0]],[[115]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
