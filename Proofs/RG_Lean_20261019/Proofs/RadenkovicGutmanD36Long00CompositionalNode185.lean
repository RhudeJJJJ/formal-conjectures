/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode184
import Proofs.RadenkovicGutmanD36Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[36,0],[0]],[[0,0],[0]],[[576,0],[0]],[[0,0],[0]],[[3852,0],[0]],[[0,0],[0]],[[13968,0],[0]],[[0,0],[0]],[[29808,0],[0]],[[0,0],[0]],[[38016,36],[36]],[[0,0],[0]],[[28044,252],[252]],[[0,0],[0]],[[10800,576],[576]],[[0,0],[0]],[[1620,468],[468]],[[0,0],[0]],[[0,108],[108]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
