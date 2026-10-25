/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode092
import Proofs.RadenkovicGutmanD43Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-3096,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-27864,-27864,0],[-27864,-26058,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-726786,-308826,0],[-308826,-84452,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-7061202,-1453572,0],[-1453572,-134762,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-37230432,-3837750,0],[-3837750,-113348,0],[0,0]],[[0,0,0],[0,0],[0]],[[-123663098,-6323924,0],[-6323924,-47816],[0]],[[0,0,0],[0,0],[0]],[[-279504558,-6817134,0],[-6817134,-6364],[0]],[[0,0,0],[0,0],[0]],[[-449303388,-4861064,0],[-4861064,2150],[0]],[[0,0,0],[0,0],[0]],[[-526805728,-2226884,0],[-2226884,860],[0]],[[0,0,0],[0,0],[0]],[[-455749862,-576544,0],[-576544,86],[0]],[[0,0],[0]],[[-290407036,-30014],[-30014]],[[0,0],[0]],[[-133516892,31820],[31820]],[[0,0],[0]],[[-41608520,10922],[10922]],[[0,0],[0]],[[-6977094,1548],[1548]],[[0,0],[0]],[[449866,86],[86]],[[0]],[[617652]],[[0]],[[176472]],[[0]],[[27262]],[[0]],[[2322]],[[0]],[[86]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
