/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode033
import Proofs.RadenkovicGutmanD13Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,507],[0,507]],[[0,0,0],[0,0,0],[0,0]],[[0,-4563,4563],[-4563,16731,2197],[4563,2197]],[[0,0,0],[0,0,0],[0,0]],[[-68445,50193,31941],[50193,114582,2704],[31941,2704]],[[0,0,0],[0,0,0],[0,0]],[[-433485,705744,88218],[705744,308087,1183],[88218,1183]],[[0,0,0],[0,0,0],[0,0]],[[237276,3193931,127933],[3193931,434330,169],[127933,169]],[[0,0,0],[0,0],[0]],[[11164647,7908186,107484],[7908186,354900],[107484]],[[0,0,0],[0,0],[0]],[[53070901,12423359,53911],[12423359,173394],[53911]],[[0,0,0],[0,0],[0]],[[140467730,13218166,15886],[13218166,49855],[15886]],[[0,0,0],[0,0],[0]],[[249332460,9823801,2535],[9823801,7774],[2535]],[[0,0,0],[0,0],[0]],[[318442475,5155683,169],[5155683,507],[169]],[[0,0],[0]],[[302898700,1901250],[1901250]],[[0,0],[0]],[[218389236,481650],[481650]],[[0,0],[0]],[[120232008,79768],[79768]],[[0,0],[0]],[[50511565,7774],[7774]],[[0,0],[0]],[[16057197,338],[338]],[[0]],[[3793374]],[[0]],[[644904]],[[0]],[[74529]],[[0]],[[5239]],[[0]],[[169]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
