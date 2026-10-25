/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode099
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e103 : NestedArithmetic.Expr 3 := .scaled (-1) e099
noncomputable def p103 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-864],[0,-864,240]],[[0,0,0],[0,0,0],[0,0]],[[0,0,-10368],[0,-35856,504],[-10368,504]],[[0,0,0],[0,0,0],[0,0]],[[-38880,-292248,-58104],[-292248,-183528,6600],[-58104,6600]],[[0,0,0],[0,0,0],[0,0]],[[-2608200,-2615976,-127512],[-2615976,-342816,8160],[-127512,8160]],[[0,0,0],[0,0,0],[0,0]],[[-28482840,-10241856,-129168],[-10241856,-224520,3384],[-129168,3384]],[[0,0,0],[0,0,0],[0,0]],[[-150807024,-22987176,-41208],[-22987176,123216,456],[-41208,456]],[[0,0,0],[0,0],[0]],[[-488326440,-32545680,33504],[-32545680,300672],[33504]],[[0,0,0],[0,0],[0]],[[-1068624168,-29990520,37944],[-29990520,208320],[37944]],[[0,0,0],[0,0],[0]],[[-1665403920,-17622768,15312],[-17622768,71928],[15312]],[[0,0,0],[0,0],[0]],[[-1902426960,-5774952,2904],[-5774952,12576],[2904]],[[0,0,0],[0,0],[0]],[[-1615065864,-241032,216],[-241032,888],[216]],[[0,0],[0]],[[-1020149376,684240],[684240]],[[0,0],[0]],[[-472630656,324336],[324336]],[[0,0],[0]],[[-153842352,73392],[73392]],[[0,0],[0]],[[-30865080,8688],[8688]],[[0,0],[0]],[[-1526760,432],[432]],[[0]],[[1175760]],[[0]],[[407856]],[[0]],[[66504]],[[0]],[[5784]],[[0]],[[216]]]
theorem step103 : p103=NestedHorner.scale (-1) p099 := by decide +kernel
#print axioms step103
theorem h103 : NestedArithmetic.compile e103=p103 := StagedExprCompile.compile_scaled (-1) e103 e099 p099 p103 rfl h099 step103
#print axioms h103
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
