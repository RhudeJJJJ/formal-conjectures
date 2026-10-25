/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode043
import Proofs.RadenkovicGutmanD14Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,588],[0,588,-336]],[[0,0,0],[0,0,0],[0,0]],[[0,5292,5292],[5292,22176,-3500],[5292,-3500]],[[0,0,0],[0,0,0],[0,0]],[[131544,220752,9828],[220752,48048,-12992],[9828,-12992]],[[0,0,0],[0,0,0],[0,0]],[[3060288,1376928,-42840],[1376928,-141680,-13412],[-42840,-13412]],[[0,0,0],[0,0,0],[0,0]],[[24799824,3560200,-178220],[3560200,-661584,-5180],[-178220,-5180]],[[0,0,0],[0,0,0],[0,0]],[[107837184,3643080,-278544],[3643080,-1064448,-672],[-278544,-672]],[[0,0,0],[0,0],[0]],[[293509048,-2554160,-235172],[-2554160,-912688],[-235172]],[[0,0,0],[0,0],[0]],[[534746016,-12859000,-115976],[-12859000,-454832],[-115976]],[[0,0,0],[0,0],[0]],[[664838720,-18885580,-33348],[-18885580,-131824],[-33348]],[[0,0,0],[0,0],[0]],[[543969608,-16320780,-5180],[-16320780,-20608],[-5180]],[[0,0,0],[0,0],[0]],[[235835432,-9295692,-336],[-9295692,-1344],[-336]],[[0,0],[0]],[[-46231080,-3592680],[-3592680]],[[0,0],[0]],[[-161185024,-935116],[-935116]],[[0,0],[0]],[[-136516016,-157192],[-157192]],[[0,0],[0]],[[-71282456,-15428],[-15428]],[[0,0],[0]],[[-25774896,-672],[-672]],[[0]],[[-6610240]],[[0]],[[-1186584]],[[0]],[[-142240]],[[0]],[[-10248]],[[0]],[[-336]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
