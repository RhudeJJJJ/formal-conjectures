/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode089
import Proofs.RadenkovicGutmanD12Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,864],[0,864,-240]],[[0,0,0],[0,0,0],[0,0]],[[0,0,10368],[0,34992,-504],[10368,-504]],[[0,0,0],[0,0,0],[0,0]],[[31104,284472,58104],[284472,176256,-6600],[58104,-6600]],[[0,0,0],[0,0,0],[0,0]],[[2405376,2529792,127512],[2529792,319248,-8160],[127512,-8160]],[[0,0,0],[0,0,0],[0,0]],[[26512272,9836208,129168],[9836208,186912,-3384],[129168,-3384]],[[0,0,0],[0,0,0],[0,0]],[[140417136,21916176,41208],[21916176,-154848,-456],[41208,-456]],[[0,0,0],[0,0],[0]],[[453815808,30780864,-33504],[30780864,-314016],[-33504]],[[0,0,0],[0,0],[0]],[[990622896,28088064,-37944],[28088064,-210096],[-37944]],[[0,0,0],[0,0],[0]],[[1540016928,16266192,-15312],[16266192,-71328],[-15312]],[[0,0,0],[0,0],[0]],[[1755411408,5153496,-2904],[5153496,-12336],[-2904]],[[0,0,0],[0,0],[0]],[[1487879856,80136,-216],[80136,-864],[-216]],[[0,0],[0]],[[939105552,-692616],[-692616]],[[0,0],[0]],[[435370128,-315456],[-315456]],[[0,0],[0]],[[142230672,-70344],[-70344]],[[0,0],[0]],[[28917984,-8256],[-8256]],[[0,0],[0]],[[1652304,-408],[-408]],[[0]],[[-1003392]],[[0]],[[-358608]],[[0]],[[-58896]],[[0]],[[-5136]],[[0]],[[-192]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
