/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode049
import Proofs.RadenkovicGutmanD10Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,10]],[[0,0],[0,0]],[[-90,150],[150,2]],[[0,0],[0]],[[1128,518],[518]],[[0,0],[0]],[[9548,588],[588]],[[0,0],[0]],[[27414,264],[264]],[[0,0],[0]],[[40700,46],[46]],[[0,0],[0]],[[35088,2],[2]],[[0]],[[18222]],[[0]],[[5662]],[[0]],[[994]],[[0]],[[84]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
