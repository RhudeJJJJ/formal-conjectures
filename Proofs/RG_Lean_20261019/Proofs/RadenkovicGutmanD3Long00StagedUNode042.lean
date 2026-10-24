/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode040
import Proofs.RadenkovicGutmanD3Long00StagedUNode041
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e042 : NestedArithmetic.Expr 3 := .plus e040 e041
noncomputable def p042 : NestedHorner.Poly 3 := [[[0],[0]],[[0,9],[9,-2]],[[0,0],[0]],[[252,21],[21]],[[0,0],[0]],[[1752,0],[0]],[[0,0],[0]],[[4918,-23],[-23]],[[0,0],[0]],[[7178,-13],[-13]],[[0,0],[0]],[[5856,-2],[-2]],[[0]],[[2642]],[[0]],[[574]],[[0]],[[14]],[[0]],[[-16]],[[0]],[[-2]]]
theorem step042 : p042=NestedHorner.add p040 p041 := by decide +kernel
#print axioms step042
theorem h042 : NestedArithmetic.compile e042=p042 := StagedExprCompile.compile_plus e042 e040 e041 p040 p041 p042 rfl h040 h041 step042
#print axioms h042
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
