/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode049
import Proofs.RadenkovicGutmanD36Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,36]],[[0,0],[0,0]],[[-324,540],[540,2]],[[0,0],[0]],[[4014,1818],[1818]],[[0,0],[0]],[[33546,1992],[1992]],[[0,0],[0]],[[95066,836],[836]],[[0,0],[0]],[[139084,124],[124]],[[0,0],[0]],[[117768,2],[2]],[[0]],[[59692]],[[0]],[[17882]],[[0]],[[2944]],[[0]],[[214]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
