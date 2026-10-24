/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode148
import Proofs.RadenkovicGutmanD2Long00CompositionalNode152
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e166 : NestedArithmetic.Expr 3 := .times e148 e152
noncomputable def p166 : NestedHorner.Poly 3 := [[[1]],[[0,0]],[[15,0]],[[0,0]],[[94,0]],[[0,0]],[[319,0]],[[0,0]],[[636,0]],[[0,0]],[[757,1]],[[0,0]],[[522,7]],[[0,0]],[[189,16]],[[0,0]],[[27,13]],[[0,0]],[[0,3]]]
theorem step166 : p166=NestedArithmetic.mul p148 p152 := by decide +kernel
#print axioms step166
theorem h166 : NestedArithmetic.compile e166=p166 := StagedExprCompile.compile_times e166 e148 e152 p148 p152 p166 rfl h148 h152 step166
#print axioms h166
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
