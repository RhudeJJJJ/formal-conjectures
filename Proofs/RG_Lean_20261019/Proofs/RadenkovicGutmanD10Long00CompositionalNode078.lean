/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode075
import Proofs.RadenkovicGutmanD10Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,100]],[[0,0],[0,0,0],[0,0]],[[0,0,900],[0,1800,1800],[900,1800]],[[0,0,0],[0,0,0],[0,0]],[[-8100,29700,15900],[29700,48000,4800],[15900,4800]],[[0,0,0],[0,0,0],[0,0]],[[102600,477900,69700],[477900,225800,4400],[69700,4400]],[[0,0,0],[0,0,0],[0,0]],[[2891700,2753100,143000],[2753100,480400,1600],[143000,1600]],[[0,0,0],[0,0,0],[0,0]],[[22284600,8474600,164400],[8474600,568800,200],[164400,200]],[[0,0,0],[0,0],[0]],[[92723900,16228300,113600],[16228300,404400],[113600]],[[0,0,0],[0,0],[0]],[[248630000,20832700,48100],[20832700,176200],[48100]],[[0,0,0],[0,0],[0]],[[466569000,18658000,12200],[18658000,46000],[12200]],[[0,0,0],[0,0],[0]],[[641741800,11893100,1700],[11893100,6600],[1700]],[[0,0,0],[0,0],[0]],[[665217000,5425700,100],[5425700,400],[100]],[[0,0],[0]],[[528386000,1757600],[1757600]],[[0,0],[0]],[[324453000,394500],[394500]],[[0,0],[0]],[[154393800,58300],[58300]],[[0,0],[0]],[[56729900,5100],[5100]],[[0,0],[0]],[[15927600,200],[200]],[[0]],[[3351000]],[[0]],[[511000]],[[0]],[[53300]],[[0]],[[3400]],[[0]],[[100]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
