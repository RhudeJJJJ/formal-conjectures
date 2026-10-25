/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode079
import Proofs.RadenkovicGutmanD33Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-58806,0],[-58806,-9801,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-970299,-852687,0],[-852687,-84942,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-15848217,-5253336,0],[-5253336,-288585,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-115142148,-18202635,0],[-18202635,-498762,0],[0,0]],[[0,0,0],[0,0],[0]],[[-494672805,-39674448,0],[-39674448,-483516],[0]],[[0,0,0],[0,0],[0]],[[-1410395481,-57735513,0],[-57735513,-272250],[0]],[[0,0,0],[0,0],[0]],[[-2839865886,-58061124,0],[-58061124,-88209],[0]],[[0,0,0],[0,0],[0]],[[-4193865324,-41107572,0],[-41107572,-15246],[0]],[[0,0,0],[0,0],[0]],[[-4653230571,-20614770,0],[-20614770,-1089],[0]],[[0,0],[0]],[[-3937969926,-7273431],[-7273431]],[[0,0],[0]],[[-2563255530,-1764180],[-1764180]],[[0,0],[0]],[[-1286509752,-279873],[-279873]],[[0,0],[0]],[[-496264923,-26136],[-26136]],[[0,0],[0]],[[-145661373,-1089],[-1089]],[[0]],[[-31918590]],[[0]],[[-5052960]],[[0]],[[-545589]],[[0]],[[-35937]],[[0]],[[-1089]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
