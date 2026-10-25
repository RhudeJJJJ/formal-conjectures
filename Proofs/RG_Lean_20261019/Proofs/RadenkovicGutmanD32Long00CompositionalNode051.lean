/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD32Long00CompositionalNode049
import Proofs.RadenkovicGutmanD32Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,32]],[[0,0],[0,0]],[[-288,480],[480,2]],[[0,0],[0]],[[3570,1618],[1618]],[[0,0],[0]],[[29854,1776],[1776]],[[0,0],[0]],[[84658,748],[748]],[[0,0],[0]],[[123948,112],[112]],[[0,0],[0]],[[105048,2],[2]],[[0]],[[53312]],[[0]],[[16002]],[[0]],[[2644]],[[0]],[[194]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree32Long00Compositional
