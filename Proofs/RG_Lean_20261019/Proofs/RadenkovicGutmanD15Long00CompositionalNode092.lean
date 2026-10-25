/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode089
import Proofs.RadenkovicGutmanD15Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1350],[0,1350,-390]],[[0,0,0],[0,0,0],[0,0]],[[0,0,16200],[0,54675,-1080],[16200,-1080]],[[0,0,0],[0,0,0],[0,0]],[[49815,444285,89370],[444285,269730,-11130],[89370,-11130]],[[0,0,0],[0,0,0],[0,0]],[[3775815,3922830,191340],[3922830,467235,-13530],[191340,-13530]],[[0,0,0],[0,0,0],[0,0]],[[41399910,15126615,183330],[15126615,218070,-5580],[183330,-5580]],[[0,0,0],[0,0,0],[0,0]],[[218292255,33349980,40710],[33349980,-336660,-750],[40710,-750]],[[0,0,0],[0,0],[0]],[[702268545,46142505,-70410],[46142505,-562890],[-70410]],[[0,0,0],[0,0],[0]],[[1525014030,41087790,-67680],[41087790,-361845],[-67680]],[[0,0,0],[0,0],[0]],[[2355890760,22645290,-26250],[22645290,-120750],[-26250]],[[0,0,0],[0,0],[0]],[[2663716725,6114180,-4890],[6114180,-20685],[-4890]],[[0,0,0],[0,0],[0]],[[2232819990,-840285,-360],[-840285,-1440],[-360]],[[0,0],[0]],[[1386347190,-1422330],[-1422330]],[[0,0],[0]],[[625603440,-575625],[-575625]],[[0,0],[0]],[[193847625,-123120],[-123120]],[[0,0],[0]],[[33865845,-14145],[-14145]],[[0,0],[0]],[[-849810,-690],[-690]],[[0]],[[-2344140]],[[0]],[[-687165]],[[0]],[[-106155]],[[0]],[[-8985]],[[0]],[[-330]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
