/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode171
import Proofs.RadenkovicGutmanD28Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e172 : NestedArithmetic.Expr 3 := .times e171 e003
noncomputable def p172 : NestedHorner.Poly 3 := [[[],[]],[[0],[0]],[[56,0],[0]],[[0,0],[0]],[[840,0],[0]],[[0,0],[0]],[[5264,0],[0]],[[0,0],[0]],[[17864,0],[0]],[[0,0],[0]],[[35616,0],[0]],[[0,0],[0]],[[42392,28],[28]],[[0,0],[0]],[[29232,196],[196]],[[0,0],[0]],[[10584,448],[448]],[[0,0],[0]],[[1512,364],[364]],[[0,0],[0]],[[0,84],[84]]]
theorem step172 : p172=NestedArithmetic.mul p171 p003 := by decide +kernel
#print axioms step172
theorem h172 : NestedArithmetic.compile e172=p172 := StagedExprCompile.compile_times e172 e171 e003 p171 p003 p172 rfl h171 h003 step172
#print axioms h172
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
