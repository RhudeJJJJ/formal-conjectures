/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode113
import Proofs.RadenkovicGutmanD33Long00CompositionalNode114
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e115 : NestedArithmetic.Expr 3 := .plus e113 e114
noncomputable def p115 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1089]],[[0,0],[0,0,0],[0,0]],[[0,0,9801],[0,0,19602],[9801,19602]],[[0,0,0],[0,0,0],[0,0]],[[88209,176418,173151],[176418,352836,52272],[173151,52272]],[[0,0,0],[0,0,0],[0,0]],[[3116718,3587166,759033],[3587166,1881792,47916],[759033,47916]],[[0,0,0],[0,0,0],[0,0]],[[41193603,22405086,1557270],[22405086,4234032,17424],[1557270,17424]],[[0,0,0],[0,0,0],[0,0]],[[269403354,72239904,1790316],[72239904,5227200,2178],[1790316,2178]],[[0,0,0],[0,0],[0]],[[1056483549,143162118,1237104],[143162118,3859416],[1237104]],[[0,0,0],[0,0],[0]],[[2762422740,189213750,523809],[189213750,1742400],[523809]],[[0,0,0],[0,0],[0]],[[5125424238,174017844,132858],[174017844,470448],[132858]],[[0,0,0],[0,0],[0]],[[7013789442,113726448,18513],[113726448,69696],[18513]],[[0,0,0],[0,0],[0]],[[7254168768,53132310,1089],[53132310,4356],[1089]],[[0,0],[0]],[[5756802480,17609130],[17609130]],[[0,0],[0]],[[3533761440,4040190],[4040190]],[[0,0],[0]],[[1681396398,609840],[609840]],[[0,0],[0]],[[617790789,54450],[54450]],[[0,0],[0]],[[173451564,2178],[2178]],[[0]],[[36492390]],[[0]],[[5564790]],[[0]],[[580437]],[[0]],[[37026]],[[0]],[[1089]]]
theorem step115 : p115=NestedHorner.add p113 p114 := by decide +kernel
#print axioms step115
theorem h115 : NestedArithmetic.compile e115=p115 := StagedExprCompile.compile_plus e115 e113 e114 p113 p114 p115 rfl h113 h114 step115
#print axioms h115
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
