/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode033
import Proofs.RadenkovicGutmanD28Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2352],[0,2352,-1456]],[[0,0,0],[0,0,0],[0,0]],[[0,-21168,21168],[-21168,77616,-16016],[21168,-16016]],[[0,0,0],[0,0,0],[0,0]],[[-199584,232848,30240],[232848,59808,-57344],[30240,-57344]],[[0,0,0],[0,0,0],[0,0]],[[33264,1151136,-219744],[1151136,-1086736,-58576],[-219744,-58576]],[[0,0,0],[0,0,0],[0,0]],[[7351344,-2165968,-821744],[-2165968,-3646048,-22512],[-821744,-22512]],[[0,0,0],[0,0,0],[0,0]],[[22090992,-24168480,-1248576],[-24168480,-5342400,-2912],[-1248576,-2912]],[[0,0,0],[0,0],[0]],[[-36881152,-71310736,-1039920],[-71310736,-4355680],[-1039920]],[[0,0,0],[0,0],[0]],[[-393339744,-118336064,-508704],[-118336064,-2098320],[-508704]],[[0,0,0],[0,0],[0]],[[-1230553184,-127609328,-145488],[-127609328,-592928],[-145488]],[[0,0,0],[0,0],[0]],[[-2324361872,-94414544,-22512],[-94414544,-90832],[-22512]],[[0,0,0],[0,0],[0]],[[-3041769472,-48907488,-1456],[-48907488,-5824],[-1456]],[[0,0],[0]],[[-2912448896,-17727360],[-17727360]],[[0,0],[0]],[[-2093834624,-4405632],[-4405632]],[[0,0],[0]],[[-1143224880,-715232],[-715232]],[[0,0],[0]],[[-474816384,-68320],[-68320]],[[0,0],[0]],[[-148945440,-2912],[-2912]],[[0]],[[-34686624]],[[0]],[[-5810224]],[[0]],[[-661472]],[[0]],[[-45808]],[[0]],[[-1456]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
