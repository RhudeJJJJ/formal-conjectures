/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode043
import Proofs.RadenkovicGutmanD25Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e096 : NestedArithmetic.Expr 3 := .times e043 e053
noncomputable def p096 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1875],[0,1875,-1150]],[[0,0,0],[0,0,0],[0,0]],[[0,16875,16875],[16875,69300,-12575],[16875,-12575]],[[0,0,0],[0,0,0],[0,0]],[[413100,691200,24975],[691200,115500,-45200],[24975,-45200]],[[0,0,0],[0,0,0],[0,0]],[[9533700,4131900,-170550],[4131900,-629200,-46225],[-170550,-46225]],[[0,0,0],[0,0,0],[0,0]],[[76108950,9736150,-644675],[9736150,-2487100,-17775],[-644675,-17775]],[[0,0,0],[0,0,0],[0,0]],[[324431100,6404850,-982500],[6404850,-3841200,-2300],[-982500,-2300]],[[0,0,0],[0,0],[0]],[[859709100,-18473800,-819525],[-18473800,-3228100],[-819525]],[[0,0,0],[0,0],[0]],[[1505876000,-54656250,-401250],[-54656250,-1588800],[-401250]],[[0,0,0],[0,0],[0]],[[1750221700,-72777275,-114825],[-72777275,-456500],[-114825]],[[0,0,0],[0,0],[0]],[[1228551550,-60248675,-17775],[-60248675,-70900],[-17775]],[[0,0,0],[0,0],[0]],[[228637450,-33475375,-1150],[-33475375,-4600],[-1150]],[[0,0],[0]],[[-562774250,-12726750],[-12726750]],[[0,0],[0]],[[-768944000,-3273375],[-3273375]],[[0,0],[0]],[[-556631800,-545250],[-545250]],[[0,0],[0]],[[-271877400,-53125],[-53125]],[[0,0],[0]],[[-94704900,-2300],[-2300]],[[0]],[[-23711500]],[[0]],[[-4185250]],[[0]],[[-495450]],[[0]],[[-35350]],[[0]],[[-1150]]]
theorem step096 : p096=NestedArithmetic.mul p043 p053 := by decide +kernel
#print axioms step096
theorem h096 : NestedArithmetic.compile e096=p096 := StagedExprCompile.compile_times e096 e043 e053 p043 p053 p096 rfl h043 h053 step096
#print axioms h096
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
