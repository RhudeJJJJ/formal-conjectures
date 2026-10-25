/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode092
import Proofs.RadenkovicGutmanD27Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1944,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-17496,-17496,0],[-17496,-16362,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-456354,-193914,0],[-193914,-53028,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4433778,-912708,0],[-912708,-84618,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-23377248,-2409750,0],[-2409750,-71172,0],[0,0]],[[0,0,0],[0,0],[0]],[[-77648922,-3970836,0],[-3970836,-30024],[0]],[[0,0,0],[0,0],[0]],[[-175502862,-4280526,0],[-4280526,-3996],[0]],[[0,0,0],[0,0],[0]],[[-282120732,-3052296,0],[-3052296,1350],[0]],[[0,0,0],[0,0],[0]],[[-330784992,-1398276,0],[-1398276,540],[0]],[[0,0,0],[0,0],[0]],[[-286168518,-362016,0],[-362016,54],[0]],[[0,0],[0]],[[-182348604,-18846],[-18846]],[[0,0],[0]],[[-83836188,19980],[19980]],[[0,0],[0]],[[-26126280,6858],[6858]],[[0,0],[0]],[[-4380966,972],[972]],[[0,0],[0]],[[282474,54],[54]],[[0]],[[387828]],[[0]],[[110808]],[[0]],[[17118]],[[0]],[[1458]],[[0]],[[54]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
