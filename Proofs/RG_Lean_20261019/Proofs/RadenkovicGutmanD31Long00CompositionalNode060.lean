/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode030
import Proofs.RadenkovicGutmanD31Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e060 : NestedArithmetic.Expr 3 := .times e030 e056
noncomputable def p060 : NestedHorner.Poly 3 := [[[0],[0]],[[0,93],[93]],[[0,0],[0]],[[1395,403],[403]],[[0,0],[0]],[[9300,496],[496]],[[0,0],[0]],[[24149,217],[217]],[[0,0],[0]],[[32736,31],[31]],[[0]],[[25668]],[[0]],[[12028]],[[0]],[[3317]],[[0]],[[496]],[[0]],[[31]]]
theorem step060 : p060=NestedArithmetic.mul p030 p056 := by decide +kernel
#print axioms step060
theorem h060 : NestedArithmetic.compile e060=p060 := StagedExprCompile.compile_times e060 e030 e056 p030 p056 p060 rfl h030 h056 step060
#print axioms h060
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
