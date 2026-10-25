/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode075
import Proofs.RadenkovicGutmanD33Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1089]],[[0,0],[0,0,0],[0,0]],[[0,0,9801],[0,19602,19602],[9801,19602]],[[0,0,0],[0,0,0],[0,0]],[[-88209,323433,173151],[323433,522720,52272],[173151,52272]],[[0,0,0],[0,0,0],[0,0]],[[1117314,5204331,759033],[5204331,2458962,47916],[759033,47916]],[[0,0,0],[0,0,0],[0,0]],[[31490613,29981259,1557270],[29981259,5231556,17424],[1557270,17424]],[[0,0,0],[0,0,0],[0,0]],[[242679294,92288394,1790316],[92288394,6194232,2178],[1790316,2178]],[[0,0,0],[0,0],[0]],[[1009763271,176726187,1237104],[176726187,4403916],[1237104]],[[0,0,0],[0,0],[0]],[[2707580700,226868103,523809],[226868103,1918818],[523809]],[[0,0,0],[0,0],[0]],[[5080936410,203185620,132858],[203185620,500940],[132858]],[[0,0,0],[0,0],[0]],[[6988568202,129515859,18513],[129515859,71874],[18513]],[[0,0,0],[0,0],[0]],[[7244213130,59085873,1089],[59085873,4356],[1089]],[[0,0],[0]],[[5754123540,19140264],[19140264]],[[0,0],[0]],[[3533293170,4296105],[4296105]],[[0,0],[0]],[[1681348482,634887],[634887]],[[0,0],[0]],[[617788611,55539],[55539]],[[0,0],[0]],[[173451564,2178],[2178]],[[0]],[[36492390]],[[0]],[[5564790]],[[0]],[[580437]],[[0]],[[37026]],[[0]],[[1089]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
