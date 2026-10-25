/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD23Long00CompositionalNode033
import Proofs.RadenkovicGutmanD23Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,529]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,12696],[0,12696,46]],[[0,0,0],[0,0,0],[0,0]],[[-42849,-28566,71415],[-28566,276138,39974],[71415,39974]],[[0,0,0],[0,0,0],[0,0]],[[-1174932,1085508,432216],[1085508,1646340,42412],[432216,42412]],[[0,0,0],[0,0,0],[0,0]],[[-5049351,10655532,1086336],[10655532,4064974,17894],[1086336,17894]],[[0,0,0],[0,0,0],[0,0]],[[12079554,42641770,1480418],[42641770,5437108,2852],[1480418,2852]],[[0,0,0],[0,0,0],[0,0]],[[173682821,98278908,1196782],[98278908,4317376,92],[1196782,92]],[[0,0,0],[0,0],[0]],[[720851556,147121708,589858],[147121708,2094932],[589858]],[[0,0,0],[0,0],[0]],[[1779726890,151347728,174984],[151347728,614238],[174984]],[[0,0,0],[0,0],[0]],[[3017555472,109964794,29302],[109964794,102396],[29302]],[[0,0,0],[0,0],[0]],[[3729347650,56988710,2323],[56988710,8234],[2323]],[[0,0,0],[0,0],[0]],[[3463000980,20978898,46],[20978898,184],[46]],[[0,0],[0]],[[2454605632,5381080],[5381080]],[[0,0],[0]],[[1336965528,923220],[923220]],[[0,0],[0]],[[559318209,97796],[97796]],[[0,0],[0]],[[178387356,5382],[5382]],[[0,0],[0]],[[42698994,92],[92]],[[0]],[[7464328]],[[0]],[[910225]],[[0]],[[71392]],[[0]],[[3059]],[[0]],[[46]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree23Long00Compositional
