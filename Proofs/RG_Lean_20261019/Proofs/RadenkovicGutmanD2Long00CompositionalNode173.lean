/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode153
import Proofs.RadenkovicGutmanD2Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .times e153 e003
noncomputable def p173 : NestedHorner.Poly 3 := [[[]],[[0]],[[1]],[[0]],[[14]],[[0]],[[81]],[[0]],[[250]],[[0]],[[444]],[[0]],[[458]],[[0]],[[265]],[[0]],[[78]],[[0]],[[9]]]
theorem step173 : p173=NestedArithmetic.mul p153 p003 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_times e173 e153 e003 p153 p003 p173 rfl h153 h003 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
