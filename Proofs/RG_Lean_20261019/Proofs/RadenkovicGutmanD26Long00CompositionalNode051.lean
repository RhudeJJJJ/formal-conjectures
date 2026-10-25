/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode049
import Proofs.RadenkovicGutmanD26Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,26]],[[0,0],[0,0]],[[-234,390],[390,2]],[[0,0],[0]],[[2904,1318],[1318]],[[0,0],[0]],[[24316,1452],[1452]],[[0,0],[0]],[[69046,616],[616]],[[0,0],[0]],[[101244,94],[94]],[[0,0],[0]],[[85968,2],[2]],[[0]],[[43742]],[[0]],[[13182]],[[0]],[[2194]],[[0]],[[164]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
