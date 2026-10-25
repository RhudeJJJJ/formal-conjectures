/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode049
import Proofs.RadenkovicGutmanD43Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,43]],[[0,0],[0,0]],[[-387,645],[645,2]],[[0,0],[0]],[[4791,2168],[2168]],[[0,0],[0]],[[40007,2370],[2370]],[[0,0],[0]],[[113280,990],[990]],[[0,0],[0]],[[165572,145],[145]],[[0,0],[0]],[[140028,2],[2]],[[0]],[[70857]],[[0]],[[21172]],[[0]],[[3469]],[[0]],[[249]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
