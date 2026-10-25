/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode049
import Proofs.RadenkovicGutmanD23Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,23]],[[0,0],[0,0]],[[-207,345],[345,2]],[[0,0],[0]],[[2571,1168],[1168]],[[0,0],[0]],[[21547,1290],[1290]],[[0,0],[0]],[[61240,550],[550]],[[0,0],[0]],[[89892,85],[85]],[[0,0],[0]],[[76428,2],[2]],[[0]],[[38957]],[[0]],[[11772]],[[0]],[[1969]],[[0]],[[149]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
