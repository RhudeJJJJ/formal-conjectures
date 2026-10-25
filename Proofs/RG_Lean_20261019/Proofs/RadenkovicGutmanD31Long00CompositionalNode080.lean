/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode035
import Proofs.RadenkovicGutmanD31Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-2883],[0,-2883]],[[0,0,0],[0,0,0],[0,0]],[[0,-25947,-25947],[-25947,-103788,-12493],[-25947,-12493]],[[0,0,0],[0,0,0],[0,0]],[[-467046,-1037880,-181629],[-1037880,-726516,-15376],[-181629,-15376]],[[0,0,0],[0,0,0],[0,0]],[[-11520468,-8649000,-501642],[-8649000,-2006568,-6727],[-501642,-6727]],[[0,0,0],[0,0,0],[0,0]],[[-102957696,-34225054,-727477],[-34225054,-2909908,-961],[-727477,-961]],[[0,0,0],[0,0],[0]],[[-500015988,-79980186,-611196],[-79980186,-2444784],[-611196]],[[0,0,0],[0,0],[0]],[[-1546400838,-121593408,-306559],[-121593408,-1226236],[-306559]],[[0,0,0],[0,0],[0]],[[-3304825184,-126400330,-90334],[-126400330,-361336],[-90334]],[[0,0,0],[0,0],[0]],[[-5118724216,-92137797,-14415],[-92137797,-57660],[-14415]],[[0,0,0],[0,0],[0]],[[-5917082654,-47508957,-961],[-47508957,-3844],[-961]],[[0,0],[0]],[[-5197505074,-17229769],[-17229769]],[[0,0],[0]],[[-3503819454,-4295670],[-4295670]],[[0,0],[0]],[[-1818980800,-700569],[-700569]],[[0,0],[0]],[[-725162912,-67270],[-67270]],[[0,0],[0]],[[-219847970,-2883],[-2883]],[[0]],[[-49737516]],[[0]],[[-8126216]],[[0]],[[-905262]],[[0]],[[-61504]],[[0]],[[-1922]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
