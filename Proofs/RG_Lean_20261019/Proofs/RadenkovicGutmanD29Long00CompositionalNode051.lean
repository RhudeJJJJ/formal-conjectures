/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode049
import Proofs.RadenkovicGutmanD29Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,29]],[[0,0],[0,0]],[[-261,435],[435,2]],[[0,0],[0]],[[3237,1468],[1468]],[[0,0],[0]],[[27085,1614],[1614]],[[0,0],[0]],[[76852,682],[682]],[[0,0],[0]],[[112596,103],[103]],[[0,0],[0]],[[95508,2],[2]],[[0]],[[48527]],[[0]],[[14592]],[[0]],[[2419]],[[0]],[[179]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
