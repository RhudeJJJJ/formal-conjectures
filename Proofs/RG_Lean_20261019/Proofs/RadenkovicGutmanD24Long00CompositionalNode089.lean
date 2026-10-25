/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode033
import Proofs.RadenkovicGutmanD24Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1728],[0,1728,-1056]],[[0,0,0],[0,0,0],[0,0]],[[0,-15552,15552],[-15552,57024,-11520],[15552,-11520]],[[0,0,0],[0,0,0],[0,0]],[[-147744,171072,23328],[171072,48384,-41472],[23328,-41472]],[[0,0,0],[0,0,0],[0,0]],[[5184,865728,-155520],[865728,-774720,-42432],[-155520,-42432]],[[0,0,0],[0,0,0],[0,0]],[[5342112,-1431360,-590400],[-1431360,-2625408,-16320],[-590400,-16320]],[[0,0,0],[0,0,0],[0,0]],[[16509888,-17183232,-900864],[-17183232,-3859200,-2112],[-900864,-2112]],[[0,0,0],[0,0],[0]],[[-24429984,-51177024,-751872],[-51177024,-3151488],[-751872]],[[0,0,0],[0,0],[0]],[[-279141504,-85248576,-368256],[-85248576,-1519680],[-368256]],[[0,0,0],[0,0],[0]],[[-881594304,-92122560,-105408],[-92122560,-429696],[-105408]],[[0,0,0],[0,0],[0]],[[-1671886272,-68251200,-16320],[-68251200,-65856],[-16320]],[[0,0,0],[0,0],[0]],[[-2192883072,-35388288,-1056],[-35388288,-4224],[-1056]],[[0,0],[0]],[[-2102782848,-12836160],[-12836160]],[[0,0],[0]],[[-1513351680,-3191808],[-3191808]],[[0,0],[0]],[[-826944960,-518400],[-518400]],[[0,0],[0]],[[-343670688,-49536],[-49536]],[[0,0],[0]],[[-107860608,-2112],[-2112]],[[0]],[[-25129152]],[[0]],[[-4210752]],[[0]],[[-479520]],[[0]],[[-33216]],[[0]],[[-1056]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
