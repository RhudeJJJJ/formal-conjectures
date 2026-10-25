/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode204
import Proofs.RadenkovicGutmanD21Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[42,0],[0]],[[0,0],[0]],[[672,0],[0]],[[0,0],[0]],[[4494,0],[0]],[[0,0],[0]],[[16296,0],[0]],[[0,0],[0]],[[34776,0],[0]],[[0,0],[0]],[[44352,42],[42]],[[0,0],[0]],[[32718,294],[294]],[[0,0],[0]],[[12600,672],[672]],[[0,0],[0]],[[1890,546],[546]],[[0,0],[0]],[[0,126],[126]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
