/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode154
import Proofs.RadenkovicGutmanD4Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e174 : NestedArithmetic.Expr 3 := .times e154 e003
noncomputable def p174 : NestedHorner.Poly 3 := [[[]],[[0]],[[1]],[[0]],[[14]],[[0]],[[81]],[[0]],[[250]],[[0]],[[444]],[[0]],[[458]],[[0]],[[265]],[[0]],[[78]],[[0]],[[9]]]
theorem step174 : p174=NestedArithmetic.mul p154 p003 := by decide +kernel
#print axioms step174
theorem h174 : NestedArithmetic.compile e174=p174 := StagedExprCompile.compile_times e174 e154 e003 p154 p003 p174 rfl h154 h003 step174
#print axioms h174
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
