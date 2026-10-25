/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode089
import Proofs.RadenkovicGutmanD20Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2400],[0,2400,-720]],[[0,0,0],[0,0,0],[0,0]],[[0,0,28800],[0,97200,-2440],[28800,-2440]],[[0,0,0],[0,0,0],[0,0]],[[90720,789480,156360],[789480,469440,-21240],[156360,-21240]],[[0,0,0],[0,0,0],[0,0]],[[6743520,6920640,326120],[6920640,774480,-25440],[326120,-25440]],[[0,0,0],[0,0,0],[0,0]],[[73554480,26460720,293040],[26460720,256160,-10440],[293040,-10440]],[[0,0,0],[0,0,0],[0,0]],[[386102640,57699440,30280],[57699440,-766880,-1400],[30280,-1400]],[[0,0,0],[0,0],[0]],[[1236355360,78559840,-157280],[78559840,-1129120],[-157280]],[[0,0,0],[0,0],[0]],[[2670541840,68067520,-135240],[68067520,-702960],[-135240]],[[0,0,0],[0,0],[0]],[[4098675680,35332720,-50800],[35332720,-231200],[-50800]],[[0,0,0],[0,0],[0]],[[4594850000,7424040,-9320],[7424040,-39280],[-9320]],[[0,0,0],[0,0],[0]],[[3805915920,-3210280,-680],[-3210280,-2720],[-680]],[[0,0],[0]],[[2320607920,-3133240],[-3133240]],[[0,0],[0]],[[1015006320,-1170400],[-1170400]],[[0,0],[0]],[[294150800,-242360],[-242360]],[[0,0],[0]],[[40084160,-27360],[-27360]],[[0,0],[0]],[[-7611280,-1320],[-1320]],[[0]],[[-5547520]],[[0]],[[-1447120]],[[0]],[[-213840]],[[0]],[[-17680]],[[0]],[[-640]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
