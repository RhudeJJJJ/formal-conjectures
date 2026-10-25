/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode049
import Proofs.RadenkovicGutmanD38Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,38]],[[0,0],[0,0]],[[-342,570],[570,2]],[[0,0],[0]],[[4236,1918],[1918]],[[0,0],[0]],[[35392,2100],[2100]],[[0,0],[0]],[[100270,880],[880]],[[0,0],[0]],[[146652,130],[130]],[[0,0],[0]],[[124128,2],[2]],[[0]],[[62882]],[[0]],[[18822]],[[0]],[[3094]],[[0]],[[224]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
