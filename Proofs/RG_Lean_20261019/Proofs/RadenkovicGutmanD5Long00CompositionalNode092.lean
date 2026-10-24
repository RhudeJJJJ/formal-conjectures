/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode089
import Proofs.RadenkovicGutmanD5Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,150],[0,150,-30]],[[0,0,0],[0,0,0],[0,0]],[[0,0,1800],[0,6075,140],[1800,140]],[[0,0,0],[0,0,0],[0,0]],[[4455,49545,11190],[49545,35010,-510],[11190,-510]],[[0,0,0],[0,0,0],[0,0]],[[404055,462510,28280],[462510,79995,-810],[28280,-810]],[[0,0,0],[0,0,0],[0,0]],[[4622670,1896255,36810],[1896255,89990,-360],[36810,-360]],[[0,0,0],[0,0,0],[0,0]],[[25240935,4500260,25570],[4500260,46780,-50],[25570,-50]],[[0,0,0],[0,0],[0]],[[84090865,6862585,8230],[6862585,1670],[8230]],[[0,0,0],[0,0],[0]],[[189743110,7054030,-60],[7054030,-10365],[-60]],[[0,0,0],[0,0],[0]],[[306552920,4978930,-850],[4978930,-5150],[-850]],[[0,0,0],[0,0],[0]],[[366291725,2402160,-230],[2402160,-1045],[-230]],[[0,0,0],[0,0],[0]],[[329862030,764855,-20],[764855,-80],[-20]],[[0,0],[0]],[[226043230,144290],[144290]],[[0,0],[0]],[[118100280,9575],[9575]],[[0,0],[0]],[[46772225,-1940],[-1940]],[[0,0],[0]],[[13823765,-465],[-465]],[[0,0],[0]],[[2955830,-30],[-30]],[[0]],[[429620]],[[0]],[[36395]],[[0]],[[765]],[[0]],[[-145]],[[0]],[[-10]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
