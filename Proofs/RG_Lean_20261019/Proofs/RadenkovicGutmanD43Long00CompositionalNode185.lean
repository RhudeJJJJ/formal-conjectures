/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode184
import Proofs.RadenkovicGutmanD43Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[43,0],[0]],[[0,0],[0]],[[688,0],[0]],[[0,0],[0]],[[4601,0],[0]],[[0,0],[0]],[[16684,0],[0]],[[0,0],[0]],[[35604,0],[0]],[[0,0],[0]],[[45408,43],[43]],[[0,0],[0]],[[33497,301],[301]],[[0,0],[0]],[[12900,688],[688]],[[0,0],[0]],[[1935,559],[559]],[[0,0],[0]],[[0,129],[129]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
