/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode095
import Proofs.RadenkovicGutmanD34Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2448,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-22032,-22032,0],[-22032,-21216,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-580176,-249696,0],[-249696,-72080,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5728320,-1211760,0],[-1211760,-124576,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-30870096,-3337440,0],[-3337440,-120768,0],[0,0]],[[0,0,0],[0,0],[0]],[[-105497648,-5834672,0],[-5834672,-68000],[0]],[[0,0,0],[0,0],[0]],[[-247378016,-6848960,0],[-6848960,-22032],[0]],[[0,0,0],[0,0],[0]],[[-417107648,-5555872,0],[-5555872,-3808],[0]],[[0,0,0],[0,0],[0]],[[-520820976,-3149760,0],[-3149760,-272],[0]],[[0,0,0],[0,0],[0]],[[-490565600,-1243312,0],[-1243312,0],[0]],[[0,0],[0]],[[-352265568,-334560],[-334560]],[[0,0],[0]],[[-193637888,-58480],[-58480]],[[0,0],[0]],[[-81309232,-5984],[-5984]],[[0,0],[0]],[[-25844080,-272],[-272]],[[0,0],[0]],[[-6105312,0],[0]],[[0]],[[-1037952]],[[0]],[[-119952]],[[0]],[[-8432]],[[0]],[[-272]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
