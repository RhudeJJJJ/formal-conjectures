/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode089
import Proofs.RadenkovicGutmanD31Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,5766],[0,5766,-1798]],[[0,0,0],[0,0,0],[0,0]],[[0,0,69192],[0,233523,-7192],[69192,-7192]],[[0,0,0],[0,0,0],[0,0]],[[223479,1895805,369210],[1895805,1102050,-54746],[369210,-54746]],[[0,0,0],[0,0,0],[0,0]],[[16280487,16490574,747596],[16490574,1717059,-64666],[747596,-64666]],[[0,0,0],[0,0,0],[0,0]],[[176598630,62469495,619938],[62469495,279062,-26412],[619938,-26412]],[[0,0,0],[0,0,0],[0,0]],[[922566975,134557980,-34906],[134557980,-2273044,-3534],[-34906,-3534]],[[0,0,0],[0,0],[0]],[[2939341601,179862217,-459978],[179862217,-3041162],[-459978]],[[0,0,0],[0,0],[0]],[[6312157070,150802414,-363072],[150802414,-1841493],[-363072]],[[0,0,0],[0,0],[0]],[[9617981384,72289706,-132618],[72289706,-597742],[-132618]],[[0,0,0],[0,0],[0]],[[10679423957,9024100,-23994],[9024100,-100781],[-23994]],[[0,0,0],[0,0],[0]],[[8725454742,-12102493,-1736],[-12102493,-6944],[-1736]],[[0,0],[0]],[[5206956726,-9074010],[-9074010]],[[0,0],[0]],[[2190021040,-3188009],[-3188009]],[[0,0],[0]],[[577627433,-642320],[-642320]],[[0,0],[0]],[[44840725,-71393],[-71393]],[[0,0],[0]],[[-33888146,-3410],[-3410]],[[0]],[[-16857676]],[[0]],[[-4053405]],[[0]],[[-577995]],[[0]],[[-46841]],[[0]],[[-1674]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
