/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode049
import Proofs.RadenkovicGutmanD42Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,42]],[[0,0],[0,0]],[[-378,630],[630,2]],[[0,0],[0]],[[4680,2118],[2118]],[[0,0],[0]],[[39084,2316],[2316]],[[0,0],[0]],[[110678,968],[968]],[[0,0],[0]],[[161788,142],[142]],[[0,0],[0]],[[136848,2],[2]],[[0]],[[69262]],[[0]],[[20702]],[[0]],[[3394]],[[0]],[[244]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
