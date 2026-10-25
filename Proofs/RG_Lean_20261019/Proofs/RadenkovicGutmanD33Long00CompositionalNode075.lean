/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode033
import Proofs.RadenkovicGutmanD33Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1089]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,19602],[0,19602]],[[0,0,0],[0,0,0],[0,0]],[[-88209,0,88209],[0,352836,52272],[88209,52272]],[[0,0,0],[0,0,0],[0,0]],[[-1528956,1587762,470448],[1587762,1881792,47916],[470448,47916]],[[0,0,0],[0,0,0],[0,0]],[[-4675077,12702096,1058508],[12702096,4234032,17424],[1058508,17424]],[[0,0,0],[0,0,0],[0,0]],[[22215600,45515844,1306800],[45515844,5227200,2178],[1306800,2178]],[[0,0,0],[0,0],[0]],[[211726647,96441840,964854],[96441840,3859416],[964854]],[[0,0,0],[0,0],[0]],[[781579656,134371710,435600],[134371710,1742400],[435600]],[[0,0,0],[0,0],[0]],[[1785496086,129530016,117612],[129530016,470448],[117612]],[[0,0,0],[0,0],[0]],[[2843392068,88505208,17424],[88505208,69696],[17424]],[[0,0,0],[0,0],[0]],[[3326036868,43176672,1089],[43176672,4356],[1089]],[[0,0],[0]],[[2936087748,14930190],[14930190]],[[0,0],[0]],[[1983234528,3571920],[3571920]],[[0,0],[0]],[[1030324680,561924],[561924]],[[0,0],[0]],[[410848119,52272],[52272]],[[0,0],[0]],[[124564176,2178],[2178]],[[0]],[[28181142]],[[0]],[[4604292]],[[0]],[[512919]],[[0]],[[34848]],[[0]],[[1089]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
