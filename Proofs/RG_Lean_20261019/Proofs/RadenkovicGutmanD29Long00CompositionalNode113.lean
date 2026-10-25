/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,841]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-15138,15138],[0,15138]],[[0,0,0],[0,0,0],[0,0]],[[68121,-136242,68121],[-136242,141288,40368],[68121,40368]],[[0,0,0],[0,0,0],[0,0]],[[-45414,-317898,363312],[-317898,1007518,37004],[363312,37004]],[[0,0,0],[0,0,0],[0,0]],[[-2520477,2316114,817452],[2316114,2499452,13456],[817452,13456]],[[0,0,0],[0,0,0],[0,0]],[[-6938250,14512296,1009200],[14512296,3289992,1682],[1009200,1682]],[[0,0,0],[0,0],[0]],[[14603965,38398378,745126],[38398378,2560004],[745126]],[[0,0,0],[0,0],[0]],[[138566524,61418230,336400],[61418230,1209358],[336400]],[[0,0,0],[0,0],[0]],[[432924934,65675372,90828],[65675372,339764],[90828]],[[0,0,0],[0,0],[0]],[[832433574,48872192,13456],[48872192,52142],[13456]],[[0,0,0],[0,0],[0]],[[1120366744,25655546,841],[25655546,3364],[841]],[[0,0],[0]],[[1110987912,9461250],[9461250]],[[0,0],[0]],[[831304952,2396850],[2396850]],[[0,0],[0]],[[474029650,396952],[396952]],[[0,0],[0]],[[206076117,38686],[38686]],[[0,0],[0]],[[67754324,1682],[1682]],[[0]],[[16549198]],[[0]],[[2908178]],[[0]],[[347333]],[[0]],[[25230]],[[0]],[[841]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
