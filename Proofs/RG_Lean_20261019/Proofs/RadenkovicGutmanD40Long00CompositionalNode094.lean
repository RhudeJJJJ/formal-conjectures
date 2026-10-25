/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD40Long00CompositionalNode035
import Proofs.RadenkovicGutmanD40Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-14400],[0,-28800,9120],[-14400,9120]],[[0,0,0],[0,0,0],[0,0]],[[0,-393120,-42720],[-393120,78720,39520],[-42720,39520]],[[0,0,0],[0,0,0],[0,0]],[[-2410560,-2030400,150560],[-2030400,1450240,48640],[150560,48640]],[[0,0,0],[0,0,0],[0,0]],[[-16692480,1972800,854080],[1972800,4881920,21280],[854080,21280]],[[0,0,0],[0,0,0],[0,0]],[[1779840,39546560,1590880],[39546560,7784320,3040],[1590880,3040]],[[0,0,0],[0,0],[0]],[[409230720,135050240,1533440],[135050240,6933760],[1533440]],[[0,0,0],[0,0],[0]],[[2062086720,248745920,840160],[248745920,3619840],[840160]],[[0,0,0],[0,0],[0]],[[5612604160,291633600,263360],[291633600,1098240],[263360]],[[0,0,0],[0,0],[0]],[[10102176640,231211680,44000],[231211680,179200],[44000]],[[0,0,0],[0,0],[0]],[[12961197760,126914080,3040],[126914080,12160],[3040]],[[0,0],[0]],[[12301274560,48318560],[48318560]],[[0,0],[0]],[[8806477760,12524800],[12524800]],[[0,0],[0]],[[4797603200,2108960],[2108960]],[[0,0],[0]],[[1989914880,208000],[208000]],[[0,0],[0]],[[623633600,9120],[9120]],[[0]],[[145127040]],[[0]],[[24295040]],[[0]],[[2764480]],[[0]],[[191360]],[[0]],[[6080]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree40Long00Compositional
