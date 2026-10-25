/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode079
import Proofs.RadenkovicGutmanD38Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-77976,0],[-77976,-12996,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1286604,-1130652,0],[-1130652,-112632,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-21014532,-6965856,0],[-6965856,-382660,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-152677008,-24136460,0],[-24136460,-661352,0],[0,0]],[[0,0,0],[0,0],[0]],[[-655929780,-52607808,0],[-52607808,-641136],[0]],[[0,0,0],[0,0],[0]],[[-1870166276,-76556548,0],[-76556548,-361000],[0]],[[0,0,0],[0,0],[0]],[[-3765625656,-76988304,0],[-76988304,-116964],[0]],[[0,0,0],[0,0],[0]],[[-5561011504,-54508112,0],[-54508112,-20216],[0]],[[0,0,0],[0,0],[0]],[[-6170123916,-27334920,0],[-27334920,-1444],[0]],[[0,0],[0]],[[-5221697496,-9644476],[-9644476]],[[0,0],[0]],[[-3398843880,-2339280],[-2339280]],[[0,0],[0]],[[-1705895392,-371108],[-371108]],[[0,0],[0]],[[-658040908,-34656],[-34656]],[[0,0],[0]],[[-193145108,-1444],[-1444]],[[0]],[[-42323640]],[[0]],[[-6700160]],[[0]],[[-723444]],[[0]],[[-47652]],[[0]],[[-1444]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
