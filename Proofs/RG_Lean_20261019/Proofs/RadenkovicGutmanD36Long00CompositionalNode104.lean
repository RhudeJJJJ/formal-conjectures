/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode092
import Proofs.RadenkovicGutmanD36Long00CompositionalNode103
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e104 : NestedArithmetic.Expr 3 := .plus e092 e103
noncomputable def p104 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2592,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-23328,-23328,0],[-23328,-21816,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-608472,-258552,0],[-258552,-70704,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5911704,-1216944,0],[-1216944,-112824,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-31169664,-3213000,0],[-3213000,-94896,0],[0,0]],[[0,0,0],[0,0],[0]],[[-103531896,-5294448,0],[-5294448,-40032],[0]],[[0,0,0],[0,0],[0]],[[-234003816,-5707368,0],[-5707368,-5328],[0]],[[0,0,0],[0,0],[0]],[[-376160976,-4069728,0],[-4069728,1800],[0]],[[0,0,0],[0,0],[0]],[[-441046656,-1864368,0],[-1864368,720],[0]],[[0,0,0],[0,0],[0]],[[-381558024,-482688,0],[-482688,72],[0]],[[0,0],[0]],[[-243131472,-25128],[-25128]],[[0,0],[0]],[[-111781584,26640],[26640]],[[0,0],[0]],[[-34835040,9144],[9144]],[[0,0],[0]],[[-5841288,1296],[1296]],[[0,0],[0]],[[376632,72],[72]],[[0]],[[517104]],[[0]],[[147744]],[[0]],[[22824]],[[0]],[[1944]],[[0]],[[72]]]
theorem step104 : p104=NestedHorner.add p092 p103 := by decide +kernel
#print axioms step104
theorem h104 : NestedArithmetic.compile e104=p104 := StagedExprCompile.compile_plus e104 e092 e103 p092 p103 p104 rfl h092 h103 step104
#print axioms h104
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
