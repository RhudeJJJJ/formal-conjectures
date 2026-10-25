/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode049
import Proofs.RadenkovicGutmanD20Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,20]],[[0,0],[0,0]],[[-180,300],[300,2]],[[0,0],[0]],[[2238,1018],[1018]],[[0,0],[0]],[[18778,1128],[1128]],[[0,0],[0]],[[53434,484],[484]],[[0,0],[0]],[[78540,76],[76]],[[0,0],[0]],[[66888,2],[2]],[[0]],[[34172]],[[0]],[[10362]],[[0]],[[1744]],[[0]],[[134]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
