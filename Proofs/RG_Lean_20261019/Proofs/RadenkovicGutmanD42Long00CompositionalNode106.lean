/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode095
import Proofs.RadenkovicGutmanD42Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-3024,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-27216,-27216,0],[-27216,-26208,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-716688,-308448,0],[-308448,-89040,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-7076160,-1496880,0],[-1496880,-153888,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-38133648,-4122720,0],[-4122720,-149184,0],[0,0]],[[0,0,0],[0,0],[0]],[[-130320624,-7207536,0],[-7207536,-84000],[0]],[[0,0,0],[0,0],[0]],[[-305584608,-8460480,0],[-8460480,-27216],[0]],[[0,0,0],[0,0],[0]],[[-515250624,-6863136,0],[-6863136,-4704],[0]],[[0,0,0],[0,0],[0]],[[-643367088,-3890880,0],[-3890880,-336],[0]],[[0,0,0],[0,0],[0]],[[-605992800,-1535856,0],[-1535856,0],[0]],[[0,0],[0]],[[-435151584,-413280],[-413280]],[[0,0],[0]],[[-239199744,-72240],[-72240]],[[0,0],[0]],[[-100440816,-7392],[-7392]],[[0,0],[0]],[[-31925040,-336],[-336]],[[0,0],[0]],[[-7541856,0],[0]],[[0]],[[-1282176]],[[0]],[[-148176]],[[0]],[[-10416]],[[0]],[[-336]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
