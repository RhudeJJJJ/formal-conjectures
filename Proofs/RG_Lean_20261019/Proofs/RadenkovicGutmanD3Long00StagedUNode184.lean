/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD3Long00StagedUNode176
import Proofs.RadenkovicGutmanD3Long00StagedUNode183
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e184 : NestedArithmetic.Expr 3 := .plus e176 e183
noncomputable def p184 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-31,0],[0,0]],[[0,0],[0,0]],[[-196,0],[0,0]],[[0,0],[0,0]],[[-641,0],[0,0]],[[0,0],[0,0]],[[-1108,0],[0,0]],[[0,0],[0,0]],[[-804,-2],[-2,0]],[[0,0],[0,0]],[[308,-13],[-13,0]],[[0,0],[0,0]],[[943,-23],[-23,0]],[[0,0],[0,0]],[[582,0],[0,0]],[[0,0],[0,0]],[[117,21],[21,0]],[[0,0],[0,0]],[[0,9],[9,-2]]]
theorem step184 : p184=NestedHorner.add p176 p183 := by decide +kernel
#print axioms step184
theorem h184 : NestedArithmetic.compile e184=p184 := StagedExprCompile.compile_plus e184 e176 e183 p176 p183 p184 rfl h176 h183 step184
#print axioms h184
end Gebendorfer.RadenkovicGutman.FixedDegree03Long00StagedU
