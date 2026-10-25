/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode049
import Proofs.RadenkovicGutmanD17Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,17]],[[0,0],[0,0]],[[-153,255],[255,2]],[[0,0],[0]],[[1905,868],[868]],[[0,0],[0]],[[16009,966],[966]],[[0,0],[0]],[[45628,418],[418]],[[0,0],[0]],[[67188,67],[67]],[[0,0],[0]],[[57348,2],[2]],[[0]],[[29387]],[[0]],[[8952]],[[0]],[[1519]],[[0]],[[119]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
