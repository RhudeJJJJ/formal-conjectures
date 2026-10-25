/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode204
import Proofs.RadenkovicGutmanD39Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e205 : NestedArithmetic.Expr 3 := .times e204 e003
noncomputable def p205 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[78,0],[0]],[[0,0],[0]],[[1248,0],[0]],[[0,0],[0]],[[8346,0],[0]],[[0,0],[0]],[[30264,0],[0]],[[0,0],[0]],[[64584,0],[0]],[[0,0],[0]],[[82368,78],[78]],[[0,0],[0]],[[60762,546],[546]],[[0,0],[0]],[[23400,1248],[1248]],[[0,0],[0]],[[3510,1014],[1014]],[[0,0],[0]],[[0,234],[234]]]
theorem step205 : p205=NestedArithmetic.mul p204 p003 := by decide +kernel
#print axioms step205
theorem h205 : NestedArithmetic.compile e205=p205 := StagedExprCompile.compile_times e205 e204 e003 p204 p003 p205 rfl h204 h003 step205
#print axioms h205
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
