/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode092
import Proofs.RadenkovicGutmanD25Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-1800,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-16200,-16200,0],[-16200,-15150,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-422550,-179550,0],[-179550,-49100,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4105350,-845100,0],[-845100,-78350,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-21645600,-2231250,0],[-2231250,-65900,0],[0,0]],[[0,0,0],[0,0],[0]],[[-71897150,-3676700,0],[-3676700,-27800],[0]],[[0,0,0],[0,0],[0]],[[-162502650,-3963450,0],[-3963450,-3700],[0]],[[0,0,0],[0,0],[0]],[[-261222900,-2826200,0],[-2826200,1250],[0]],[[0,0,0],[0,0],[0]],[[-306282400,-1294700,0],[-1294700,500],[0]],[[0,0,0],[0,0],[0]],[[-264970850,-335200,0],[-335200,50],[0]],[[0,0],[0]],[[-168841300,-17450],[-17450]],[[0,0],[0]],[[-77626100,18500],[18500]],[[0,0],[0]],[[-24191000,6350],[6350]],[[0,0],[0]],[[-4056450,900],[900]],[[0,0],[0]],[[261550,50],[50]],[[0]],[[359100]],[[0]],[[102600]],[[0]],[[15850]],[[0]],[[1350]],[[0]],[[50]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
