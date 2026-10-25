/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode095
import Proofs.RadenkovicGutmanD43Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-3096,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-27864,-27864,0],[-27864,-26832,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-733752,-315792,0],[-315792,-91160,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-7244640,-1532520,0],[-1532520,-157552,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-39041592,-4220880,0],[-4220880,-152736,0],[0,0]],[[0,0,0],[0,0],[0]],[[-133423496,-7379144,0],[-7379144,-86000],[0]],[[0,0,0],[0,0],[0]],[[-312860432,-8661920,0],[-8661920,-27864],[0]],[[0,0,0],[0,0],[0]],[[-527518496,-7026544,0],[-7026544,-4816],[0]],[[0,0,0],[0,0],[0]],[[-658685352,-3983520,0],[-3983520,-344],[0]],[[0,0,0],[0,0],[0]],[[-620421200,-1572424,0],[-1572424,0],[0]],[[0,0],[0]],[[-445512336,-423120],[-423120]],[[0,0],[0]],[[-244894976,-73960],[-73960]],[[0,0],[0]],[[-102832264,-7568],[-7568]],[[0,0],[0]],[[-32685160,-344],[-344]],[[0,0],[0]],[[-7721424,0],[0]],[[0]],[[-1312704]],[[0]],[[-151704]],[[0]],[[-10664]],[[0]],[[-344]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
