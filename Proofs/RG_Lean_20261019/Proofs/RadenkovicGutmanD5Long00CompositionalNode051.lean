/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode049
import Proofs.RadenkovicGutmanD5Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,5]],[[0,0],[0,0]],[[-45,75],[75,2]],[[0,0],[0]],[[573,268],[268]],[[0,0],[0]],[[4933,318],[318]],[[0,0],[0]],[[14404,154],[154]],[[0,0],[0]],[[21780,31],[31]],[[0,0],[0]],[[19188,2],[2]],[[0]],[[10247]],[[0]],[[3312]],[[0]],[[619]],[[0]],[[59]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
