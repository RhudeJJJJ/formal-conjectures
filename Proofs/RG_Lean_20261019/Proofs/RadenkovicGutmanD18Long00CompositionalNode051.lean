/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode049
import Proofs.RadenkovicGutmanD18Long00CompositionalNode050
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e051 : NestedArithmetic.Expr 3 := .plus e049 e050
noncomputable def p051 : NestedHorner.Poly 3 := [[[0],[0,18]],[[0,0],[0,0]],[[-162,270],[270,2]],[[0,0],[0]],[[2016,918],[918]],[[0,0],[0]],[[16932,1020],[1020]],[[0,0],[0]],[[48230,440],[440]],[[0,0],[0]],[[70972,70],[70]],[[0,0],[0]],[[60528,2],[2]],[[0]],[[30982]],[[0]],[[9422]],[[0]],[[1594]],[[0]],[[124]],[[0]],[[2]]]
theorem step051 : p051=NestedHorner.add p049 p050 := by decide +kernel
#print axioms step051
theorem h051 : NestedArithmetic.compile e051=p051 := StagedExprCompile.compile_plus e051 e049 e050 p049 p050 p051 rfl h049 h050 step051
#print axioms h051
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
