/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD7Long00CompositionalNode071
import Proofs.RadenkovicGutmanD7Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-2646,0],[-2646,-945,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-48195,-53487,0],[-53487,-10080,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1008315,-442386,0],[-442386,-44205,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-9242478,-2026871,0],[-2026871,-103740,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-49631925,-5810798,0],[-5810798,-142800,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-175802347,-11111541,0],[-11111541,-119490,0],[0,0]],[[0,0,0],[0,0],[0]],[[-437987004,-14714210,0],[-14714210,-61005],[0]],[[0,0,0],[0,0],[0]],[[-798436184,-13795964,0],[-13795964,-18480],[0]],[[0,0,0],[0,0],[0]],[[-1092889371,-9260622,0],[-9260622,-3045],[0]],[[0,0,0],[0,0],[0]],[[-1142492372,-4455647,0],[-4455647,-210],[0]],[[0,0,0],[0,0],[0]],[[-921871958,-1521338,0],[-1521338,0],[0]],[[0,0],[0]],[[-577223892,-359373],[-359373]],[[0,0],[0]],[[-280584563,-55790],[-55790]],[[0,0],[0]],[[-105378539,-5117],[-5117]],[[0,0],[0]],[[-30239748,-210],[-210]],[[0,0],[0]],[[-6500060,0],[0]],[[0]],[[-1012109]],[[0]],[[-107723]],[[0]],[[-7007]],[[0]],[[-210]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree07Long00Compositional
