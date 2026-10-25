/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode096
import Proofs.RadenkovicGutmanD20Long00CompositionalNode098
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .plus e096 e098
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2400],[0,2400,-720]],[[0,0,0],[0,0,0],[0,0]],[[0,0,28800],[0,98640,-2440],[28800,-2440]],[[0,0,0],[0,0,0],[0,0]],[[103680,802440,156360],[802440,481560,-21240],[156360,-21240]],[[0,0,0],[0,0,0],[0,0]],[[7081560,7064280,326120],[7064280,813760,-25440],[326120,-25440]],[[0,0,0],[0,0,0],[0,0]],[[76838760,27136800,293040],[27136800,318840,-10440],[293040,-10440]],[[0,0,0],[0,0,0],[0,0]],[[403419120,59484440,30280],[59484440,-714160,-1400],[30280,-1400]],[[0,0,0],[0,0],[0]],[[1293873080,81501200,-157280],[81501200,-1106880],[-157280]],[[0,0,0],[0,0],[0]],[[2800543960,71238280,-135240],[71238280,-700000],[-135240]],[[0,0,0],[0,0],[0]],[[4307654000,37593680,-50800],[37593680,-232200],[-50800]],[[0,0,0],[0,0],[0]],[[4839875920,8459800,-9320],[8459800,-39680],[-9320]],[[0,0,0],[0,0],[0]],[[4017892600,-2942120,-680],[-2942120,-2760],[-680]],[[0,0],[0]],[[2455680960,-3119280],[-3119280]],[[0,0],[0]],[[1077107200,-1185200],[-1185200]],[[0,0],[0]],[[313503600,-247440],[-247440]],[[0,0],[0]],[[43329320,-28080],[-28080]],[[0,0],[0]],[[-7820520,-1360],[-1360]],[[0]],[[-5834800]],[[0]],[[-1529200]],[[0]],[[-226520]],[[0]],[[-18760]],[[0]],[[-680]]]
theorem step099 : p099=NestedHorner.add p096 p098 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_plus e099 e096 e098 p096 p098 p099 rfl h096 h098 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
