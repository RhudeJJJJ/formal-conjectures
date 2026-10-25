/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode065
import Proofs.RadenkovicGutmanD27Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e074 : NestedArithmetic.Expr 3 := .times e065 e057
noncomputable def p074 : NestedHorner.Poly 3 := [[[0],[0]],[[0,81],[81]],[[0,0],[0]],[[1215,351],[351]],[[0,0],[0]],[[8100,432],[432]],[[0,0],[0]],[[21033,189],[189]],[[0,0],[0]],[[28512,27],[27]],[[0]],[[22356]],[[0]],[[10476]],[[0]],[[2889]],[[0]],[[432]],[[0]],[[27]]]
theorem step074 : p074=NestedArithmetic.mul p065 p057 := by decide +kernel
#print axioms step074
theorem h074 : NestedArithmetic.compile e074=p074 := StagedExprCompile.compile_times e074 e065 e057 p065 p057 p074 rfl h065 h057 step074
#print axioms h074
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
