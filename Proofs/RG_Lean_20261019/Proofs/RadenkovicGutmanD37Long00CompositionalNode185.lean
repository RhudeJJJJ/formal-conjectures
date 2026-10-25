/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode184
import Proofs.RadenkovicGutmanD37Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[37,0],[0]],[[0,0],[0]],[[592,0],[0]],[[0,0],[0]],[[3959,0],[0]],[[0,0],[0]],[[14356,0],[0]],[[0,0],[0]],[[30636,0],[0]],[[0,0],[0]],[[39072,37],[37]],[[0,0],[0]],[[28823,259],[259]],[[0,0],[0]],[[11100,592],[592]],[[0,0],[0]],[[1665,481],[481]],[[0,0],[0]],[[0,111],[111]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
