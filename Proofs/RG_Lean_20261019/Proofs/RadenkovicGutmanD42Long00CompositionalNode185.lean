/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode184
import Proofs.RadenkovicGutmanD42Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e185 : NestedArithmetic.Expr 3 := .times e184 e003
noncomputable def p185 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[42,0],[0]],[[0,0],[0]],[[672,0],[0]],[[0,0],[0]],[[4494,0],[0]],[[0,0],[0]],[[16296,0],[0]],[[0,0],[0]],[[34776,0],[0]],[[0,0],[0]],[[44352,42],[42]],[[0,0],[0]],[[32718,294],[294]],[[0,0],[0]],[[12600,672],[672]],[[0,0],[0]],[[1890,546],[546]],[[0,0],[0]],[[0,126],[126]]]
theorem step185 : p185=NestedArithmetic.mul p184 p003 := by decide +kernel
#print axioms step185
theorem h185 : NestedArithmetic.compile e185=p185 := StagedExprCompile.compile_times e185 e184 e003 p184 p003 p185 rfl h184 h003 step185
#print axioms h185
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
