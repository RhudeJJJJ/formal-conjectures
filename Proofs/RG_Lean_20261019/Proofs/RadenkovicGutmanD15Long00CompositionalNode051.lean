/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode049
import Proofs.RadenkovicGutmanD15Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,15]],[[0,0],[0,0]],[[-135,225],[225,2]],[[0,0],[0]],[[1683,768],[768]],[[0,0],[0]],[[14163,858],[858]],[[0,0],[0]],[[40424,374],[374]],[[0,0],[0]],[[59620,61],[61]],[[0,0],[0]],[[50988,2],[2]],[[0]],[[26197]],[[0]],[[8012]],[[0]],[[1369]],[[0]],[[109]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
