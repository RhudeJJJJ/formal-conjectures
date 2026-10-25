/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode049
import Proofs.RadenkovicGutmanD8Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,8]],[[0,0],[0,0]],[[-72,120],[120,2]],[[0,0],[0]],[[906,418],[418]],[[0,0],[0]],[[7702,480],[480]],[[0,0],[0]],[[22210,220],[220]],[[0,0],[0]],[[33132,40],[40]],[[0,0],[0]],[[28728,2],[2]],[[0]],[[15032]],[[0]],[[4722]],[[0]],[[844]],[[0]],[[74]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
