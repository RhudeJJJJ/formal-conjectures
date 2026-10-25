/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode030
import Proofs.RadenkovicGutmanD27Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e060 : NestedArithmetic.Expr 3 := .times e030 e056
noncomputable def p060 : NestedHorner.Poly 3 := [[[0],[0]],[[0,81],[81]],[[0,0],[0]],[[1215,351],[351]],[[0,0],[0]],[[8100,432],[432]],[[0,0],[0]],[[21033,189],[189]],[[0,0],[0]],[[28512,27],[27]],[[0]],[[22356]],[[0]],[[10476]],[[0]],[[2889]],[[0]],[[432]],[[0]],[[27]]]
theorem step060 : p060=NestedArithmetic.mul p030 p056 := by decide +kernel
#print axioms step060
theorem h060 : NestedArithmetic.compile e060=p060 := StagedExprCompile.compile_times e060 e030 e056 p030 p056 p060 rfl h030 h056 step060
#print axioms h060
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
