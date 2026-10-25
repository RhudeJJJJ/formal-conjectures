/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode203
import Proofs.RadenkovicGutmanD26Long00CompositionalNode205
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e206 : NestedArithmetic.Expr 3 := .plus e203 e205
noncomputable def p206 : NestedHorner.Poly 3 := [[[2],[0]],[[0,0],[0]],[[112,0],[0,0]],[[0,0],[0,0]],[[1518,0],[0,0]],[[0,0],[0,0]],[[9698,0],[0,0]],[[0,0],[0,0]],[[34954,0],[0,0]],[[0,0],[0,0]],[[75880,2],[2,0]],[[0,0],[0,0]],[[100516,94],[94,0]],[[0,0],[0,0]],[[79082,616],[616,0]],[[0,0],[0,0]],[[34040,1452],[1452,0]],[[0,0],[0,0]],[[6492,1318],[1318,0]],[[0,0],[0,0]],[[234,390],[390,2]],[[0],[0,0]],[[0],[0,26]]]
theorem step206 : p206=NestedHorner.add p203 p205 := by decide +kernel
#print axioms step206
theorem h206 : NestedArithmetic.compile e206=p206 := StagedExprCompile.compile_plus e206 e203 e205 p203 p205 p206 rfl h203 h205 step206
#print axioms h206
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
