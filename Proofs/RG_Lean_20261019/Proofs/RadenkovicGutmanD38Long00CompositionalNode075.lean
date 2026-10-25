/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD38Long00CompositionalNode033
import Proofs.RadenkovicGutmanD38Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1444]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,25992],[0,25992]],[[0,0,0],[0,0,0],[0,0]],[[-116964,0,116964],[0,467856,69312],[116964,69312]],[[0,0,0],[0,0,0],[0,0]],[[-2027376,2105352,623808],[2105352,2495232,63536],[623808,63536]],[[0,0,0],[0,0,0],[0,0]],[[-6199092,16842816,1403568],[16842816,5614272,23104],[1403568,23104]],[[0,0,0],[0,0,0],[0,0]],[[29457600,60353424,1732800],[60353424,6931200,2888],[1732800,2888]],[[0,0,0],[0,0],[0]],[[280746812,127880640,1279384],[127880640,5117536],[1279384]],[[0,0,0],[0,0],[0]],[[1036364576,178175160,577600],[178175160,2310400],[577600]],[[0,0,0],[0,0],[0]],[[2367544856,171755136,155952],[171755136,623808],[155952]],[[0,0,0],[0,0],[0]],[[3770301328,117356768,23104],[117356768,92416],[23104]],[[0,0,0],[0,0],[0]],[[4410282128,57251712,1444],[57251712,5776],[1444]],[[0,0],[0]],[[3893214608,19797240],[19797240]],[[0,0],[0]],[[2629743488,4736320],[4736320]],[[0,0],[0]],[[1366197280,745104],[745104]],[[0,0],[0]],[[544779324,69312],[69312]],[[0,0],[0]],[[165170496,2888],[2888]],[[0]],[[37367832]],[[0]],[[6105232]],[[0]],[[680124]],[[0]],[[46208]],[[0]],[[1444]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree38Long00Compositional
