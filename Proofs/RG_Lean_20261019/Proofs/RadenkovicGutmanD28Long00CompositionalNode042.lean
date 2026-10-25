/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode030
import Proofs.RadenkovicGutmanD28Long00CompositionalNode028
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e042 : NestedArithmetic.Expr 3 := .times e030 e028
noncomputable def p042 : NestedHorner.Poly 3 := [[[0],[0]],[[0,84],[84]],[[0,0],[0]],[[1512,364],[364]],[[0,0],[0]],[[10584,448],[448]],[[0,0],[0]],[[29232,196],[196]],[[0,0],[0]],[[42392,28],[28]],[[0]],[[35616]],[[0]],[[17864]],[[0]],[[5264]],[[0]],[[840]],[[0]],[[56]]]
theorem step042 : p042=NestedArithmetic.mul p030 p028 := by decide +kernel
#print axioms step042
theorem h042 : NestedArithmetic.compile e042=p042 := StagedExprCompile.compile_times e042 e030 e028 p030 p028 p042 rfl h030 h028 step042
#print axioms h042
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
