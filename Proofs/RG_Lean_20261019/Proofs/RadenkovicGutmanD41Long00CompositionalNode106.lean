/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD41Long00CompositionalNode095
import Proofs.RadenkovicGutmanD41Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2952,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-26568,-26568,0],[-26568,-25584,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-699624,-301104,0],[-301104,-86920,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6907680,-1461240,0],[-1461240,-150224,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-37225704,-4024560,0],[-4024560,-145632,0],[0,0]],[[0,0,0],[0,0],[0]],[[-127217752,-7035928,0],[-7035928,-82000],[0]],[[0,0,0],[0,0],[0]],[[-298308784,-8259040,0],[-8259040,-26568],[0]],[[0,0,0],[0,0],[0]],[[-502982752,-6699728,0],[-6699728,-4592],[0]],[[0,0,0],[0,0],[0]],[[-628048824,-3798240,0],[-3798240,-328],[0]],[[0,0,0],[0,0],[0]],[[-591564400,-1499288,0],[-1499288,0],[0]],[[0,0],[0]],[[-424790832,-403440],[-403440]],[[0,0],[0]],[[-233504512,-70520],[-70520]],[[0,0],[0]],[[-98049368,-7216],[-7216]],[[0,0],[0]],[[-31164920,-328],[-328]],[[0,0],[0]],[[-7362288,0],[0]],[[0]],[[-1251648]],[[0]],[[-144648]],[[0]],[[-10168]],[[0]],[[-328]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree41Long00Compositional
