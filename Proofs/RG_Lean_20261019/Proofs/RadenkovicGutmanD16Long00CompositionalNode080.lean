/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode035
import Proofs.RadenkovicGutmanD16Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-768],[0,-768]],[[0,0,0],[0,0,0],[0,0]],[[0,-6912,-6912],[-6912,-27648,-3328],[-6912,-3328]],[[0,0,0],[0,0,0],[0,0]],[[-124416,-276480,-48384],[-276480,-193536,-4096],[-48384,-4096]],[[0,0,0],[0,0,0],[0,0]],[[-3068928,-2304000,-133632],[-2304000,-534528,-1792],[-133632,-1792]],[[0,0,0],[0,0,0],[0,0]],[[-27426816,-9117184,-193792],[-9117184,-775168,-256],[-193792,-256]],[[0,0,0],[0,0],[0]],[[-133198848,-21305856,-162816],[-21305856,-651264],[-162816]],[[0,0,0],[0,0],[0]],[[-411944448,-32391168,-81664],[-32391168,-326656],[-81664]],[[0,0,0],[0,0],[0]],[[-880369664,-33671680,-24064],[-33671680,-96256],[-24064]],[[0,0,0],[0,0],[0]],[[-1363572736,-24544512,-3840],[-24544512,-15360],[-3840]],[[0,0,0],[0,0],[0]],[[-1576246784,-12655872,-256],[-12655872,-1024],[-256]],[[0,0],[0]],[[-1384559104,-4589824],[-4589824]],[[0,0],[0]],[[-933379584,-1144320],[-1144320]],[[0,0],[0]],[[-484556800,-186624],[-186624]],[[0,0],[0]],[[-193175552,-17920],[-17920]],[[0,0],[0]],[[-58565120,-768],[-768]],[[0]],[[-13249536]],[[0]],[[-2164736]],[[0]],[[-241152]],[[0]],[[-16384]],[[0]],[[-512]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
