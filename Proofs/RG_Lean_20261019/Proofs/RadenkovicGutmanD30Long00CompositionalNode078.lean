/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD30Long00CompositionalNode075
import Proofs.RadenkovicGutmanD30Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,900]],[[0,0],[0,0,0],[0,0]],[[0,0,8100],[0,16200,16200],[8100,16200]],[[0,0,0],[0,0,0],[0,0]],[[-72900,267300,143100],[267300,432000,43200],[143100,43200]],[[0,0,0],[0,0,0],[0,0]],[[923400,4301100,627300],[4301100,2032200,39600],[627300,39600]],[[0,0,0],[0,0,0],[0,0]],[[26025300,24777900,1287000],[24777900,4323600,14400],[1287000,14400]],[[0,0,0],[0,0,0],[0,0]],[[200561400,76271400,1479600],[76271400,5119200,1800],[1479600,1800]],[[0,0,0],[0,0],[0]],[[834515100,146054700,1022400],[146054700,3639600],[1022400]],[[0,0,0],[0,0],[0]],[[2237670000,187494300,432900],[187494300,1585800],[432900]],[[0,0,0],[0,0],[0]],[[4199121000,167922000,109800],[167922000,414000],[109800]],[[0,0,0],[0,0],[0]],[[5775676200,107037900,15300],[107037900,59400],[15300]],[[0,0,0],[0,0],[0]],[[5986953000,48831300,900],[48831300,3600],[900]],[[0,0],[0]],[[4755474000,15818400],[15818400]],[[0,0],[0]],[[2920077000,3550500],[3550500]],[[0,0],[0]],[[1389544200,524700],[524700]],[[0,0],[0]],[[510569100,45900],[45900]],[[0,0],[0]],[[143348400,1800],[1800]],[[0]],[[30159000]],[[0]],[[4599000]],[[0]],[[479700]],[[0]],[[30600]],[[0]],[[900]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree30Long00Compositional
