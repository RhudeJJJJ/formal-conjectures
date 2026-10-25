/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode033
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e113 : NestedArithmetic.Expr 3 := .pow e033 2
noncomputable def p113 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,441]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,-7938,7938],[0,7938]],[[0,0,0],[0,0,0],[0,0]],[[35721,-71442,35721],[-71442,74088,21168],[35721,21168]],[[0,0,0],[0,0,0],[0,0]],[[-23814,-166698,190512],[-166698,528318,19404],[190512,19404]],[[0,0,0],[0,0,0],[0,0]],[[-1321677,1214514,428652],[1214514,1310652,7056],[428652,7056]],[[0,0,0],[0,0,0],[0,0]],[[-3638250,7609896,529200],[7609896,1725192,882],[529200,882]],[[0,0,0],[0,0],[0]],[[7657965,20135178,390726],[20135178,1342404],[390726]],[[0,0,0],[0,0],[0]],[[72660924,32206230,176400],[32206230,634158],[176400]],[[0,0,0],[0,0],[0]],[[227015334,34438572,47628],[34438572,178164],[47628]],[[0,0,0],[0,0],[0]],[[436507974,25627392,7056],[25627392,27342],[7056]],[[0,0,0],[0,0],[0]],[[587493144,13453146,441],[13453146,1764],[441]],[[0,0],[0]],[[582575112,4961250],[4961250]],[[0,0],[0]],[[435916152,1256850],[1256850]],[[0,0],[0]],[[248569650,208152],[208152]],[[0,0],[0]],[[108061317,20286],[20286]],[[0,0],[0]],[[35528724,882],[882]],[[0]],[[8677998]],[[0]],[[1524978]],[[0]],[[182133]],[[0]],[[13230]],[[0]],[[441]]]
theorem step113 : p113=NestedArithmetic.power p033 2 := by decide +kernel
#print axioms step113
theorem h113 : NestedArithmetic.compile e113=p113 := StagedExprCompile.compile_pow 2 e113 e033 p033 p113 rfl h033 step113
#print axioms h113
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
