/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode043
import Proofs.RadenkovicGutmanD26Long00CompositionalNode066
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e071 : NestedArithmetic.Expr 3 := .times e043 e066
noncomputable def p071 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-2028],[0,-2028,1248]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-18252,-30420],[-18252,-99216,21008],[-30420,21008,96]],[[0,0,0],[0,0,0],[0,0]],[[-446472,-1228500,-66144],[-1228500,-92496,82588],[-66144,82588]],[[0,0,0],[0,0,0],[0,0]],[[-14798808,-8407512,297676],[-8407512,1656208,93892],[297676,93892]],[[0,0,0],[0,0,0],[0,0]],[[-136839888,-22629088,1399348],[-22629088,6074880,40624],[1399348,40624]],[[0,0,0],[0,0,0],[0,0]],[[-644010096,-20901568,2410796],[-20901568,9600912,6476],[2410796,6476]],[[0,0,0],[0,0,0],[0,0]],[[-1849489480,32115120,2221668],[32115120,8395344,192],[2221668,192]],[[0,0,0],[0,0],[0]],[[-3485457896,123500992,1190836],[123500992,4337520],[1190836]],[[0,0,0],[0,0],[0]],[[-4367891808,181909636,373852],[181909636,1326880],[373852]],[[0,0,0],[0,0],[0]],[[-3392000632,162277648,64968],[162277648,227200],[64968]],[[0,0,0],[0,0],[0]],[[-971522976,96321344,5228],[96321344,18400],[5228]],[[0,0,0],[0,0],[0]],[[1211751776,39047988,96],[39047988,384],[96]],[[0,0],[0]],[[1974532664,10753356],[10753356]],[[0,0],[0]],[[1543326272,1944396],[1944396]],[[0,0],[0]],[[799718104,213556],[213556]],[[0,0],[0]],[[294297272,11924],[11924]],[[0,0],[0]],[[77995216,192],[192]],[[0]],[[14692424]],[[0]],[[1892376]],[[0]],[[154024]],[[0]],[[6696]],[[0]],[[96]]]
theorem step071 : p071=NestedArithmetic.mul p043 p066 := by decide +kernel
#print axioms step071
theorem h071 : NestedArithmetic.compile e071=p071 := StagedExprCompile.compile_times e071 e043 e066 p043 p066 p071 rfl h043 h066 step071
#print axioms h071
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
