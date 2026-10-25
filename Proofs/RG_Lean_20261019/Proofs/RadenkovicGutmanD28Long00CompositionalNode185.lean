/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode184
import Proofs.RadenkovicGutmanD28Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[28,0],[0]],[[0,0],[0]],[[448,0],[0]],[[0,0],[0]],[[2996,0],[0]],[[0,0],[0]],[[10864,0],[0]],[[0,0],[0]],[[23184,0],[0]],[[0,0],[0]],[[29568,28],[28]],[[0,0],[0]],[[21812,196],[196]],[[0,0],[0]],[[8400,448],[448]],[[0,0],[0]],[[1260,364],[364]],[[0,0],[0]],[[0,84],[84]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
