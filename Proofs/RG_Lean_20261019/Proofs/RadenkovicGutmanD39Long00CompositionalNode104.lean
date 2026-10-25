/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode092
import Proofs.RadenkovicGutmanD39Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2808,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-25272,-25272,0],[-25272,-23634,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-659178,-280098,0],[-280098,-76596,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6404346,-1318356,0],[-1318356,-122226,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-33767136,-3480750,0],[-3480750,-102804,0],[0,0]],[[0,0,0],[0,0],[0]],[[-112159554,-5735652,0],[-5735652,-43368],[0]],[[0,0,0],[0,0],[0]],[[-253504134,-6182982,0],[-6182982,-5772],[0]],[[0,0,0],[0,0],[0]],[[-407507724,-4408872,0],[-4408872,1950],[0]],[[0,0,0],[0,0],[0]],[[-477800544,-2019732,0],[-2019732,780],[0]],[[0,0,0],[0,0],[0]],[[-413354526,-522912,0],[-522912,78],[0]],[[0,0],[0]],[[-263392428,-27222],[-27222]],[[0,0],[0]],[[-121096716,28860],[28860]],[[0,0],[0]],[[-37737960,9906],[9906]],[[0,0],[0]],[[-6328062,1404],[1404]],[[0,0],[0]],[[408018,78],[78]],[[0]],[[560196]],[[0]],[[160056]],[[0]],[[24726]],[[0]],[[2106]],[[0]],[[78]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
