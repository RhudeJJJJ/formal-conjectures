/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode033
import Proofs.RadenkovicGutmanD20Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,400]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,7200],[0,7200]],[[0,0,0],[0,0,0],[0,0]],[[-32400,0,32400],[0,129600,19200],[32400,19200]],[[0,0,0],[0,0,0],[0,0]],[[-561600,583200,172800],[583200,691200,17600],[172800,17600]],[[0,0,0],[0,0,0],[0,0]],[[-1717200,4665600,388800],[4665600,1555200,6400],[388800,6400]],[[0,0,0],[0,0,0],[0,0]],[[8160000,16718400,480000],[16718400,1920000,800],[480000,800]],[[0,0,0],[0,0],[0]],[[77769200,35424000,354400],[35424000,1417600],[354400]],[[0,0,0],[0,0],[0]],[[287081600,49356000,160000],[49356000,640000],[160000]],[[0,0,0],[0,0],[0]],[[655829600,47577600,43200],[47577600,172800],[43200]],[[0,0,0],[0,0],[0]],[[1044404800,32508800,6400],[32508800,25600],[6400]],[[0,0,0],[0,0],[0]],[[1221684800,15859200,400],[15859200,1600],[400]],[[0,0],[0]],[[1078452800,5484000],[5484000]],[[0,0],[0]],[[728460800,1312000],[1312000]],[[0,0],[0]],[[378448000,206400],[206400]],[[0,0],[0]],[[150908400,19200],[19200]],[[0,0],[0]],[[45753600,800],[800]],[[0]],[[10351200]],[[0]],[[1691200]],[[0]],[[188400]],[[0]],[[12800]],[[0]],[[400]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
