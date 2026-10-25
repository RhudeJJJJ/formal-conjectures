/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode035
import Proofs.RadenkovicGutmanD29Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-2523],[0,-2523]],[[0,0,0],[0,0,0],[0,0]],[[0,-22707,-22707],[-22707,-90828,-10933],[-22707,-10933]],[[0,0,0],[0,0,0],[0,0]],[[-408726,-908280,-158949],[-908280,-635796,-13456],[-158949,-13456]],[[0,0,0],[0,0,0],[0,0]],[[-10081908,-7569000,-439002],[-7569000,-1756008,-5887],[-439002,-5887]],[[0,0,0],[0,0,0],[0,0]],[[-90101376,-29951374,-636637],[-29951374,-2546548,-841],[-636637,-841]],[[0,0,0],[0,0],[0]],[[-437579028,-69993066,-534876],[-69993066,-2139504],[-534876]],[[0,0,0],[0,0],[0]],[[-1353301878,-106410048,-268279],[-106410048,-1073116],[-268279]],[[0,0,0],[0,0],[0]],[[-2892151904,-110616730,-79054],[-110616730,-316216],[-79054]],[[0,0,0],[0,0],[0]],[[-4479549496,-80632557,-12615],[-80632557,-50460],[-12615]],[[0,0,0],[0,0],[0]],[[-5178216974,-41576517,-841],[-41576517,-3364],[-841]],[[0,0],[0]],[[-4548492994,-15078289],[-15078289]],[[0,0],[0]],[[-3066297774,-3759270],[-3759270]],[[0,0],[0]],[[-1591844800,-613089],[-613089]],[[0,0],[0]],[[-634611872,-58870],[-58870]],[[0,0],[0]],[[-192395570,-2523],[-2523]],[[0]],[[-43526796]],[[0]],[[-7111496]],[[0]],[[-792222]],[[0]],[[-53824]],[[0]],[[-1682]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
