/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode184
import Proofs.RadenkovicGutmanD27Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[27,0],[0]],[[0,0],[0]],[[432,0],[0]],[[0,0],[0]],[[2889,0],[0]],[[0,0],[0]],[[10476,0],[0]],[[0,0],[0]],[[22356,0],[0]],[[0,0],[0]],[[28512,27],[27]],[[0,0],[0]],[[21033,189],[189]],[[0,0],[0]],[[8100,432],[432]],[[0,0],[0]],[[1215,351],[351]],[[0,0],[0]],[[0,81],[81]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
