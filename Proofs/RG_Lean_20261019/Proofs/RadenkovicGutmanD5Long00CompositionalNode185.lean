/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode184
import Proofs.RadenkovicGutmanD5Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[5,0],[0]],[[0,0],[0]],[[80,0],[0]],[[0,0],[0]],[[535,0],[0]],[[0,0],[0]],[[1940,0],[0]],[[0,0],[0]],[[4140,0],[0]],[[0,0],[0]],[[5280,5],[5]],[[0,0],[0]],[[3895,35],[35]],[[0,0],[0]],[[1500,80],[80]],[[0,0],[0]],[[225,65],[65]],[[0,0],[0]],[[0,15],[15]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
