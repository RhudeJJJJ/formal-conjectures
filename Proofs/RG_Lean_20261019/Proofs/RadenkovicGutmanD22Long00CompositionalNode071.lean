/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode043
import Proofs.RadenkovicGutmanD22Long00CompositionalNode066
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e071 : NestedArithmetic.Expr 3 := .times e043 e066
noncomputable def p071 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-1452],[0,-1452,880]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-13068,-21780],[-13068,-71280,14696],[-21780,14696,80]],[[0,0,0],[0,0,0],[0,0]],[[-320760,-882684,-49368],[-882684,-76176,58244],[-49368,58244]],[[0,0,0],[0,0,0],[0,0]],[[-10649880,-6098904,201796],[-6098904,1135056,66628],[201796,66628]],[[0,0,0],[0,0,0],[0,0]],[[-98859744,-16747936,975940],[-16747936,4239200,29128],[975940,29128]],[[0,0,0],[0,0,0],[0,0]],[[-467645184,-16836720,1695156],[-16836720,6748656,4756],[1695156,4756]],[[0,0,0],[0,0,0],[0,0]],[[-1352148216,19144352,1570660],[19144352,5934096,160],[1570660,160]],[[0,0,0],[0,0],[0]],[[-2573381768,83270080,846380],[83270080,3084080],[846380]],[[0,0,0],[0,0],[0]],[[-3278842816,125585332,267532],[125585332,950912],[267532]],[[0,0,0],[0,0],[0]],[[-2643042552,113328344,47008],[113328344,164928],[47008]],[[0,0,0],[0,0],[0]],[[-921608080,67806568,3876],[67806568,13728],[3876]],[[0,0,0],[0,0],[0]],[[688010416,27681372,80],[27681372,320],[80]],[[0,0],[0]],[[1305940456,7679804],[7679804]],[[0,0],[0]],[[1056576544,1401684],[1401684]],[[0,0],[0]],[[556753736,156164],[156164]],[[0,0],[0]],[[207201912,8972],[8972]],[[0,0],[0]],[[55431760,160],[160]],[[0]],[[10541576]],[[0]],[[1373368]],[[0]],[[113656]],[[0]],[[5096]],[[0]],[[80]]]
theorem step071 : p071=NestedArithmetic.mul p043 p066 := by decide +kernel
#print axioms step071
theorem h071 : NestedArithmetic.compile e071=p071 := StagedExprCompile.compile_times e071 e043 e066 p043 p066 p071 rfl h043 h066 step071
#print axioms h071
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
