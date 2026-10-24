/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode017
import Proofs.RadenkovicGutmanD2Long00CompositionalNode054
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e058 : NestedArithmetic.Expr 3 := .times e017 e054
noncomputable def p058 : NestedHorner.Poly 3 := [[[0],[0]],[[0,6],[6]],[[0,0],[0]],[[90,26],[26]],[[0,0],[0]],[[600,32],[32]],[[0,0],[0]],[[1558,14],[14]],[[0,0],[0]],[[2112,2],[2]],[[0]],[[1656]],[[0]],[[776]],[[0]],[[214]],[[0]],[[32]],[[0]],[[2]]]
theorem step058 : p058=NestedArithmetic.mul p017 p054 := by decide +kernel
#print axioms step058
theorem h058 : NestedArithmetic.compile e058=p058 := StagedExprCompile.compile_times e058 e017 e054 p017 p054 p058 rfl h017 h054 step058
#print axioms h058
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
