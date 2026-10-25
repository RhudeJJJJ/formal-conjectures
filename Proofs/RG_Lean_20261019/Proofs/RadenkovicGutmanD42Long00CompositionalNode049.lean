/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode045
import Proofs.RadenkovicGutmanD42Long00CompositionalNode048
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e049 : NestedArithmetic.Expr 3 := .plus e045 e048
noncomputable def p049 : NestedHorner.Poly 3 := [[[0],[0,42]],[[0,0],[0,0]],[[-378,630],[630,2]],[[0,0],[0]],[[4644,2118],[2118]],[[0,0],[0]],[[38772,2316],[2316]],[[0,0],[0]],[[109618,968],[968]],[[0,0],[0]],[[159956,142],[142]],[[0,0],[0]],[[135072,2],[2]],[[0]],[[68262]],[[0]],[[20378]],[[0]],[[3338]],[[0]],[[240]],[[0]],[[2]]]
theorem step049 : p049=NestedHorner.add p045 p048 := by decide +kernel
#print axioms step049
theorem h049 : NestedArithmetic.compile e049=p049 := StagedExprCompile.compile_plus e049 e045 e048 p045 p048 p049 rfl h045 h048 step049
#print axioms h049
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
