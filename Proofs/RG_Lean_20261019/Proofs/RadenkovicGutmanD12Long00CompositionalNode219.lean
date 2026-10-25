/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode065
import Proofs.RadenkovicGutmanD12Long00CompositionalNode218
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e219 : NestedArithmetic.Expr 3 := .times e065 e218
noncomputable def p219 : NestedHorner.Poly 3 := [[[12],[0]],[[0,0],[0]],[[192,0],[0]],[[0,0],[0]],[[1284,0],[0]],[[0,0],[0]],[[4656,0],[0]],[[0,0],[0]],[[9936,0],[0]],[[0,0],[0]],[[12672,12],[12]],[[0,0],[0]],[[9348,84],[84]],[[0,0],[0]],[[3600,192],[192]],[[0,0],[0]],[[540,156],[156]],[[0,0],[0]],[[0,36],[36]]]
theorem step219 : p219=NestedArithmetic.mul p065 p218 := by decide +kernel
#print axioms step219
theorem h219 : NestedArithmetic.compile e219=p219 := StagedExprCompile.compile_times e219 e065 e218 p065 p218 p219 rfl h065 h218 step219
#print axioms h219
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
