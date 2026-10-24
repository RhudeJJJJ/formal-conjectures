/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode159
import Proofs.RadenkovicGutmanD4Long00CompositionalNode161
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e162 : NestedArithmetic.Expr 3 := .plus e159 e161
noncomputable def p162 : NestedHorner.Poly 3 := [[[-2],[0]],[[0,0],[0]],[[-26,0],[0,0]],[[0,0],[0,0]],[[-132,0],[0,0]],[[0,0],[0,0]],[[-314,0],[0,0]],[[0,0],[0,0]],[[-272,0],[0,0]],[[0,0],[0,0]],[[264,-2],[-2,0]],[[0,0],[0,0]],[[804,-16],[-16,0]],[[0,0],[0,0]],[[726,-44],[-44,0]],[[0,0],[0,0]],[[306,-48],[-48,0]],[[0,0],[0,0]],[[54,-18],[-18,0]],[[0],[0,0]],[[0],[0,-2]]]
theorem step162 : p162=NestedHorner.add p159 p161 := by decide +kernel
#print axioms step162
theorem h162 : NestedArithmetic.compile e162=p162 := StagedExprCompile.compile_plus e162 e159 e161 p159 p161 p162 rfl h159 h161 step162
#print axioms h162
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
