/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode049
import Proofs.RadenkovicGutmanD24Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,24]],[[0,0],[0,0]],[[-216,360],[360,2]],[[0,0],[0]],[[2682,1218],[1218]],[[0,0],[0]],[[22470,1344],[1344]],[[0,0],[0]],[[63842,572],[572]],[[0,0],[0]],[[93676,88],[88]],[[0,0],[0]],[[79608,2],[2]],[[0]],[[40552]],[[0]],[[12242]],[[0]],[[2044]],[[0]],[[154]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
