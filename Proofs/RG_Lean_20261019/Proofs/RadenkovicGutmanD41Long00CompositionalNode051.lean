/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode049
import Proofs.RadenkovicGutmanD41Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,41]],[[0,0],[0,0]],[[-369,615],[615,2]],[[0,0],[0]],[[4569,2068],[2068]],[[0,0],[0]],[[38161,2262],[2262]],[[0,0],[0]],[[108076,946],[946]],[[0,0],[0]],[[158004,139],[139]],[[0,0],[0]],[[133668,2],[2]],[[0]],[[67667]],[[0]],[[20232]],[[0]],[[3319]],[[0]],[[239]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
