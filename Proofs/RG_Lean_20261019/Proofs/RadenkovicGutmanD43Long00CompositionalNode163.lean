/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode160
import Proofs.RadenkovicGutmanD43Long00CompositionalNode162
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e163 : NestedArithmetic.Expr 3 := .plus e160 e162
noncomputable def p163 : NestedHorner.Poly 3 := [[[-41],[0]],[[0,0],[0]],[[-611,0],[0,0]],[[0,0],[0,0]],[[-3798,0],[0,0]],[[0,0],[0,0]],[[-12755,0],[0,0]],[[0,0],[0,0]],[[-25076,0],[0,0]],[[0,0],[0,0]],[[-29220,-41],[-41,0]],[[0,0],[0,0]],[[-19242,-328],[-328,0]],[[0,0],[0,0]],[[-5787,-902],[-902,0]],[[0,0],[0,0]],[[189,-984],[-984,0]],[[0,0],[0,0]],[[405,-369],[-369,0]],[[0],[0,0]],[[0],[0,-41]]]
theorem step163 : p163=NestedHorner.add p160 p162 := by decide +kernel
#print axioms step163
theorem h163 : NestedArithmetic.compile e163=p163 := StagedExprCompile.compile_plus e163 e160 e162 p160 p162 p163 rfl h160 h162 step163
#print axioms h163
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
