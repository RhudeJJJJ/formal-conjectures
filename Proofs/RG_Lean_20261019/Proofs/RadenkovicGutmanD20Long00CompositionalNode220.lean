/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode217
import Proofs.RadenkovicGutmanD20Long00CompositionalNode219
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e220 : NestedArithmetic.Expr 3 := .times e217 e219
noncomputable def p220 : NestedHorner.Poly 3 := [[[-800],[0],[0]],[[0,0],[0,0],[0]],[[-24800,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-352800,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-3052800,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-17956800,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-76011200,-1200,0],[-1200,0],[0]],[[0,0,0],[0,0],[0]],[[-239127200,-26800,0],[-26800,0],[0]],[[0,0,0],[0,0],[0]],[[-569351200,-266000,0],[-266000,0],[0]],[[0,0,0],[0,0],[0]],[[-1035091200,-1546400,0],[-1546400,0],[0]],[[0,0,0],[0,0],[0]],[[-1439183200,-5843600,0],[-5843600,0],[0]],[[0,0,0],[0,0],[0]],[[-1522562400,-15063600,-400],[-15063600,-800],[-400]],[[0,0,0],[0,0],[0]],[[-1210446400,-27054400,-5600],[-27054400,-11200],[-5600]],[[0,0,0],[0,0],[0]],[[-707438400,-33974800,-32400],[-33974800,-64800],[-32400]],[[0,0,0],[0,0],[0]],[[-293126400,-29489200,-100000],[-29489200,-200000],[-100000]],[[0,0,0],[0,0],[0]],[[-80978400,-17180000,-177600],[-17180000,-355200],[-177600]],[[0,0,0],[0,0],[0]],[[-13284000,-6346800,-183200],[-6346800,-366400],[-183200]],[[0,0,0],[0,0],[0]],[[-972000,-1328400,-106000],[-1328400,-212000],[-106000]],[[0,0,0],[0,0],[0]],[[0,-118800,-31200],[-118800,-62400],[-31200]],[[0,0,0],[0,0],[0]],[[0,0,-3600],[0,-7200],[-3600]]]
theorem step220 : p220=NestedArithmetic.mul p217 p219 := by decide +kernel
#print axioms step220
theorem h220 : NestedArithmetic.compile e220=p220 := StagedExprCompile.compile_times e220 e217 e219 p217 p219 p220 rfl h217 h219 step220
#print axioms h220
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
