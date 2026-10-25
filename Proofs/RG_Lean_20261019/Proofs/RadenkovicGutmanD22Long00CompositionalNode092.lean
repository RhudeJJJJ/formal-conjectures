/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode089
import Proofs.RadenkovicGutmanD22Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2904],[0,2904,-880]],[[0,0,0],[0,0,0],[0,0]],[[0,0,34848],[0,117612,-3124],[34848,-3124]],[[0,0,0],[0,0,0],[0,0]],[[110484,955152,188364],[955152,564696,-26180],[188364,-26180]],[[0,0,0],[0,0,0],[0,0]],[[8169876,8356392,389972],[8356392,918588,-31240],[389972,-31240]],[[0,0,0],[0,0,0],[0,0]],[[88985952,31875228,343728],[31875228,266552,-12804],[343728,-12804]],[[0,0,0],[0,0,0],[0,0]],[[466533276,69291816,22748],[69291816,-983488,-1716],[22748,-1716]],[[0,0,0],[0,0],[0]],[[1491989708,93911884,-200904],[93911884,-1408616],[-200904]],[[0,0,0],[0,0],[0]],[[3217959536,80719144,-168564],[80719144,-870276],[-168564]],[[0,0,0],[0,0],[0]],[[4929837968,41127152,-62832],[41127152,-285208],[-62832]],[[0,0,0],[0,0],[0]],[[5513355188,7846036,-11484],[7846036,-48356],[-11484]],[[0,0,0],[0,0],[0]],[[4551189456,-4450864,-836],[-4450864,-3344],[-836]],[[0,0],[0]],[[2760412512,-3990756],[-3990756]],[[0,0],[0]],[[1196089048,-1464716],[-1464716]],[[0,0],[0]],[[339268292,-301004],[-301004]],[[0,0],[0]],[[41861644,-33836],[-33836]],[[0,0],[0]],[[-11222816,-1628],[-1628]],[[0]],[[-7167952]],[[0]],[[-1825428]],[[0]],[[-267036]],[[0]],[[-21956]],[[0]],[[-792]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
