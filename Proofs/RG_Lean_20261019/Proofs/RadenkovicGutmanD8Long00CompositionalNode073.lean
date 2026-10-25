/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode071
import Proofs.RadenkovicGutmanD8Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-3456,0],[-3456,-1152,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-62208,-69120,0],[-69120,-12432,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1297296,-569232,0],[-569232,-55136,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-11874384,-2604512,0],[-2604512,-130704,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-63739584,-7467248,0],[-7467248,-181408,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-225813840,-14288864,0],[-14288864,-152768,0],[0,0]],[[0,0,0],[0,0],[0]],[[-562862896,-18939312,0],[-18939312,-78368],[0]],[[0,0,0],[0,0],[0]],[[-1026756192,-17774912,0],[-17774912,-23824],[0]],[[0,0,0],[0,0],[0]],[[-1406435648,-11942944,0],[-11942944,-3936],[0]],[[0,0,0],[0,0],[0]],[[-1471368688,-5751360,0],[-5751360,-272],[0]],[[0,0,0],[0,0],[0]],[[-1188114400,-1965360,0],[-1965360,0],[0]],[[0,0],[0]],[[-744456032,-464608],[-464608]],[[0,0],[0]],[[-362117504,-72176],[-72176]],[[0,0],[0]],[[-136085296,-6624],[-6624]],[[0,0],[0]],[[-39074416,-272],[-272]],[[0,0],[0]],[[-8403680,0],[0]],[[0]],[[-1309184]],[[0]],[[-139408]],[[0]],[[-9072]],[[0]],[[-272]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
