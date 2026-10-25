/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode075
import Proofs.RadenkovicGutmanD20Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,400]],[[0,0],[0,0,0],[0,0]],[[0,0,3600],[0,7200,7200],[3600,7200]],[[0,0,0],[0,0,0],[0,0]],[[-32400,118800,63600],[118800,192000,19200],[63600,19200]],[[0,0,0],[0,0,0],[0,0]],[[410400,1911600,278800],[1911600,903200,17600],[278800,17600]],[[0,0,0],[0,0,0],[0,0]],[[11566800,11012400,572000],[11012400,1921600,6400],[572000,6400]],[[0,0,0],[0,0,0],[0,0]],[[89138400,33898400,657600],[33898400,2275200,800],[657600,800]],[[0,0,0],[0,0],[0]],[[370895600,64913200,454400],[64913200,1617600],[454400]],[[0,0,0],[0,0],[0]],[[994520000,83330800,192400],[83330800,704800],[192400]],[[0,0,0],[0,0],[0]],[[1866276000,74632000,48800],[74632000,184000],[48800]],[[0,0,0],[0,0],[0]],[[2566967200,47572400,6800],[47572400,26400],[6800]],[[0,0,0],[0,0],[0]],[[2660868000,21702800,400],[21702800,1600],[400]],[[0,0],[0]],[[2113544000,7030400],[7030400]],[[0,0],[0]],[[1297812000,1578000],[1578000]],[[0,0],[0]],[[617575200,233200],[233200]],[[0,0],[0]],[[226919600,20400],[20400]],[[0,0],[0]],[[63710400,800],[800]],[[0]],[[13404000]],[[0]],[[2044000]],[[0]],[[213200]],[[0]],[[13600]],[[0]],[[400]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
