/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode204
import Proofs.RadenkovicGutmanD8Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[16,0],[0]],[[0,0],[0]],[[256,0],[0]],[[0,0],[0]],[[1712,0],[0]],[[0,0],[0]],[[6208,0],[0]],[[0,0],[0]],[[13248,0],[0]],[[0,0],[0]],[[16896,16],[16]],[[0,0],[0]],[[12464,112],[112]],[[0,0],[0]],[[4800,256],[256]],[[0,0],[0]],[[720,208],[208]],[[0,0],[0]],[[0,48],[48]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
