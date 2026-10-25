/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD33Long00CompositionalNode184
import Proofs.RadenkovicGutmanD33Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[33,0],[0]],[[0,0],[0]],[[528,0],[0]],[[0,0],[0]],[[3531,0],[0]],[[0,0],[0]],[[12804,0],[0]],[[0,0],[0]],[[27324,0],[0]],[[0,0],[0]],[[34848,33],[33]],[[0,0],[0]],[[25707,231],[231]],[[0,0],[0]],[[9900,528],[528]],[[0,0],[0]],[[1485,429],[429]],[[0,0],[0]],[[0,99],[99]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree33Long00Compositional
