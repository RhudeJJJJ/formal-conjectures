/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode160
import Proofs.RadenkovicGutmanD9Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-7],[0]],[[0,0],[0]],[[-101,0],[0,0]],[[0,0],[0,0]],[[-602,0],[0,0]],[[0,0],[0,0]],[[-1909,0],[0,0]],[[0,0],[0,0]],[[-3452,0],[0,0]],[[0,0],[0,0]],[[-3516,-7],[-7,0]],[[0,0],[0,0]],[[-1766,-56],[-56,0]],[[0,0],[0,0]],[[-109,-154],[-154,0]],[[0,0],[0,0]],[[291,-168],[-168,0]],[[0,0],[0,0]],[[99,-63],[-63,0]],[[0],[0,0]],[[0],[0,-7]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
