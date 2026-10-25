/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode184
import Proofs.RadenkovicGutmanD14Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[14,0],[0]],[[0,0],[0]],[[224,0],[0]],[[0,0],[0]],[[1498,0],[0]],[[0,0],[0]],[[5432,0],[0]],[[0,0],[0]],[[11592,0],[0]],[[0,0],[0]],[[14784,14],[14]],[[0,0],[0]],[[10906,98],[98]],[[0,0],[0]],[[4200,224],[224]],[[0,0],[0]],[[630,182],[182]],[[0,0],[0]],[[0,42],[42]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
