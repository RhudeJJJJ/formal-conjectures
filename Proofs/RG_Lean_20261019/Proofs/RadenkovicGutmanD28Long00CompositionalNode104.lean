/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode092
import Proofs.RadenkovicGutmanD28Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2016,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-18144,-18144,0],[-18144,-16968,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-473256,-201096,0],[-201096,-54992,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4597992,-946512,0],[-946512,-87752,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-24243072,-2499000,0],[-2499000,-73808,0],[0,0]],[[0,0,0],[0,0],[0]],[[-80524808,-4117904,0],[-4117904,-31136],[0]],[[0,0,0],[0,0],[0]],[[-182002968,-4439064,0],[-4439064,-4144],[0]],[[0,0,0],[0,0],[0]],[[-292569648,-3165344,0],[-3165344,1400],[0]],[[0,0,0],[0,0],[0]],[[-343036288,-1450064,0],[-1450064,560],[0]],[[0,0,0],[0,0],[0]],[[-296767352,-375424,0],[-375424,56],[0]],[[0,0],[0]],[[-189102256,-19544],[-19544]],[[0,0],[0]],[[-86941232,20720],[20720]],[[0,0],[0]],[[-27093920,7112],[7112]],[[0,0],[0]],[[-4543224,1008],[1008]],[[0,0],[0]],[[292936,56],[56]],[[0]],[[402192]],[[0]],[[114912]],[[0]],[[17752]],[[0]],[[1512]],[[0]],[[56]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
