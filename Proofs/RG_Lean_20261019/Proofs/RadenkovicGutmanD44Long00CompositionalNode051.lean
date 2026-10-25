/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode049
import Proofs.RadenkovicGutmanD44Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,44]],[[0,0],[0,0]],[[-396,660],[660,2]],[[0,0],[0]],[[4902,2218],[2218]],[[0,0],[0]],[[40930,2424],[2424]],[[0,0],[0]],[[115882,1012],[1012]],[[0,0],[0]],[[169356,148],[148]],[[0,0],[0]],[[143208,2],[2]],[[0]],[[72452]],[[0]],[[21642]],[[0]],[[3544]],[[0]],[[254]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
