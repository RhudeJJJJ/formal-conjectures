/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,100]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1800,1800],[0,1800]],[[0,0,0],[0,0,0],[0,0]],[[8100,-16200,8100],[-16200,16800,4800],[8100,4800]],[[0,0,0],[0,0,0],[0,0]],[[-5400,-37800,43200],[-37800,119800,4400],[43200,4400]],[[0,0,0],[0,0,0],[0,0]],[[-299700,275400,97200],[275400,297200,1600],[97200,1600]],[[0,0,0],[0,0,0],[0,0]],[[-825000,1725600,120000],[1725600,391200,200],[120000,200]],[[0,0,0],[0,0],[0]],[[1736500,4565800,88600],[4565800,304400],[88600]],[[0,0,0],[0,0],[0]],[[16476400,7303000,40000],[7303000,143800],[40000]],[[0,0,0],[0,0],[0]],[[51477400,7809200,10800],[7809200,40400],[10800]],[[0,0,0],[0,0],[0]],[[98981400,5811200,1600],[5811200,6200],[1600]],[[0,0,0],[0,0],[0]],[[133218400,3050600,100],[3050600,400],[100]],[[0,0],[0]],[[132103200,1125000],[1125000]],[[0,0],[0]],[[98847200,285000],[285000]],[[0,0],[0]],[[56365000,47200],[47200]],[[0,0],[0]],[[24503700,4600],[4600]],[[0,0],[0]],[[8056400,200],[200]],[[0]],[[1967800]],[[0]],[[345800]],[[0]],[[41300]],[[0]],[[3000]],[[0]],[[100]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
