/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode091
import Proofs.RadenkovicGutmanD2Long00CompositionalNode092
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .plus e091 e092
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,4]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-36],[0,-72,96],[-36,96,4]],[[0,0,0],[0,0,0],[0,0]],[[-324,-1404,228],[-1404,1464,368],[228,368]],[[0,0,0],[0,0,0],[0,0]],[[-18900,-5076,2504],[-5076,11512,496],[2504,496]],[[0,0,0],[0,0,0],[0,0]],[[-176148,22428,7960],[22428,33384,296],[7960,296]],[[0,0,0],[0,0,0],[0,0]],[[-734124,193232,12968],[193232,51760,80],[12968,80]],[[0,0,0],[0,0,0],[0,0]],[[-1543468,600884,12432],[600884,48176,8],[12432,8]],[[0,0,0],[0,0],[0]],[[-913644,1096140,7372],[1096140,28136],[7372]],[[0,0,0],[0,0],[0]],[[3974008,1324504,2728],[1324504,10376],[2728]],[[0,0,0],[0,0],[0]],[[13579440,1115260,612],[1115260,2344],[612]],[[0,0,0],[0,0],[0]],[[23343264,669300,76],[669300,296],[76]],[[0,0,0],[0,0],[0]],[[26988864,287968,4],[287968,16],[4]],[[0,0],[0]],[[22713576,88100],[88100]],[[0,0],[0]],[[14369272,18692],[18692]],[[0,0],[0]],[[6924532,2612],[2612]],[[0,0],[0]],[[2547156,216],[216]],[[0,0],[0]],[[710088,8],[8]],[[0]],[[147424]],[[0]],[[22076]],[[0]],[[2252]],[[0]],[[140]],[[0]],[[4]]]
theorem step093 : p093=NestedHorner.add p091 p092 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_plus e093 e091 e092 p091 p092 p093 rfl h091 h092 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
