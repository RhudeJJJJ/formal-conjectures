/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode217
import Proofs.RadenkovicGutmanD39Long00CompositionalNode219
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e220 : NestedArithmetic.Expr 3 := .times e217 e219
noncomputable def p220 : NestedHorner.Poly 3 := [[[-3042],[0],[0]],[[0,0],[0,0],[0]],[[-94302,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-1341522,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-11608272,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-68280732,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-289032588,-4563,0],[-4563,0],[0]],[[0,0,0],[0,0],[0]],[[-909281178,-101907,0],[-101907,0],[0]],[[0,0,0],[0,0],[0]],[[-2164957938,-1011465,0],[-1011465,0],[0]],[[0,0,0],[0,0],[0]],[[-3935934288,-5880186,0],[-5880186,0],[0]],[[0,0,0],[0,0],[0]],[[-5472494118,-22220289,0],[-22220289,0],[0]],[[0,0,0],[0,0],[0]],[[-5789543526,-57279339,-1521],[-57279339,-3042],[-1521]],[[0,0,0],[0,0],[0]],[[-4602722436,-102874356,-21294],[-102874356,-42588],[-21294]],[[0,0,0],[0,0],[0]],[[-2690034516,-129189177,-123201],[-129189177,-246402],[-123201]],[[0,0,0],[0,0],[0]],[[-1114613136,-112132683,-380250],[-112132683,-760500],[-380250]],[[0,0,0],[0,0],[0]],[[-307920366,-65326950,-675324],[-65326950,-1350648],[-675324]],[[0,0,0],[0,0],[0]],[[-50512410,-24133707,-696618],[-24133707,-1393236],[-696618]],[[0,0,0],[0,0],[0]],[[-3696030,-5051241,-403065],[-5051241,-806130],[-403065]],[[0,0,0],[0,0],[0]],[[0,-451737,-118638],[-451737,-237276],[-118638]],[[0,0,0],[0,0],[0]],[[0,0,-13689],[0,-27378],[-13689]]]
theorem step220 : p220=NestedArithmetic.mul p217 p219 := by decide +kernel
#print axioms step220
theorem h220 : NestedArithmetic.compile e220=p220 := StagedExprCompile.compile_times e220 e217 e219 p217 p219 p220 rfl h217 h219 step220
#print axioms h220
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
