/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode049
import Proofs.RadenkovicGutmanD31Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,31]],[[0,0],[0,0]],[[-279,465],[465,2]],[[0,0],[0]],[[3459,1568],[1568]],[[0,0],[0]],[[28931,1722],[1722]],[[0,0],[0]],[[82056,726],[726]],[[0,0],[0]],[[120164,109],[109]],[[0,0],[0]],[[101868,2],[2]],[[0]],[[51717]],[[0]],[[15532]],[[0]],[[2569]],[[0]],[[189]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
