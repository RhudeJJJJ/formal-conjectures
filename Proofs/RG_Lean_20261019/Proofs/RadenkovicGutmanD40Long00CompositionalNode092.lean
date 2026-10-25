/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode089
import Proofs.RadenkovicGutmanD40Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,9600],[0,9600,-3040]],[[0,0,0],[0,0,0],[0,0]],[[0,0,115200],[0,388800,-12880],[115200,-12880]],[[0,0,0],[0,0,0],[0,0]],[[375840,3155760,610320],[3155760,1817280,-93680],[610320,-93680]],[[0,0,0],[0,0,0],[0,0]],[[27159840,27362880,1220240],[27362880,2760960,-110080],[1220240,-110080]],[[0,0,0],[0,0,0],[0,0]],[[293945760,103256640,974880],[103256640,235520,-44880],[974880,-44880]],[[0,0,0],[0,0,0],[0,0]],[[1532575680,221261280,-131440],[221261280,-4077760,-6000],[-131440,-6000]],[[0,0,0],[0,0],[0]],[[4872689120,293411680,-821760],[293411680,-5287040],[-821760]],[[0,0,0],[0,0],[0]],[[10438602080,242405440,-630480],[242405440,-3169920],[-630480]],[[0,0,0],[0,0],[0]],[[15857255360,111777440,-228000],[111777440,-1024000],[-228000]],[[0,0,0],[0,0],[0]],[[17535521600,9022480,-41040],[9022480,-172160],[-41040]],[[0,0,0],[0,0],[0]],[[14242412640,-23139760,-2960],[-23139760,-11840],[-2960]],[[0,0],[0]],[[8418375840,-16160880],[-16160880]],[[0,0],[0]],[[3476959840,-5564000],[-5564000]],[[0,0],[0]],[[873800000,-1110320],[-1110320]],[[0,0],[0]],[[39605920,-122720],[-122720]],[[0,0],[0]],[[-67048160,-5840],[-5840]],[[0]],[[-30471040]],[[0]],[[-7141440]],[[0]],[[-1006080]],[[0]],[[-80960]],[[0]],[[-2880]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
