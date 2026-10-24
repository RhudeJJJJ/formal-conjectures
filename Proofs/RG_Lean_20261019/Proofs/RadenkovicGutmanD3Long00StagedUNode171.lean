/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode163
import Proofs.RadenkovicGutmanD3Long00StagedUNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e171 : NestedArithmetic.Expr 3 := .plus e163 e170
noncomputable def p171 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-16,0],[0,0]],[[0,0],[0,0]],[[14,0],[0,0]],[[0,0],[0,0]],[[574,0],[0,0]],[[0,0],[0,0]],[[2642,0],[0,0]],[[0,0],[0,0]],[[5856,-2],[-2,0]],[[0,0],[0,0]],[[7178,-13],[-13,0]],[[0,0],[0,0]],[[4918,-23],[-23,0]],[[0,0],[0,0]],[[1752,0],[0,0]],[[0,0],[0,0]],[[252,21],[21,0]],[[0,0],[0,0]],[[0,9],[9,-2]]]
theorem step171 : p171=NestedHorner.add p163 p170 := by decide +kernel
#print axioms step171
theorem h171 : NestedArithmetic.compile e171=p171 := StagedExprCompile.compile_plus e171 e163 e170 p163 p170 p171 rfl h163 h170 step171
#print axioms h171
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
