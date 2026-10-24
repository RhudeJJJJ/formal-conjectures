/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode057
import Proofs.RadenkovicGutmanD2Long00CompositionalNode058
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e059 : NestedArithmetic.Expr 3 := .plus e057 e058
noncomputable def p059 : NestedHorner.Poly 3 := [[[0],[0]],[[0,6],[6,0]],[[0,0],[0]],[[90,26],[26]],[[0,0],[0]],[[600,32],[32]],[[0,0],[0]],[[1558,14],[14]],[[0,0],[0]],[[2112,2],[2]],[[0,0],[0]],[[1656,0],[0]],[[0]],[[776]],[[0]],[[214]],[[0]],[[32]],[[0]],[[2]],[[0]],[[0]]]
theorem step059 : p059=NestedHorner.add p057 p058 := by decide +kernel
#print axioms step059
theorem h059 : NestedArithmetic.compile e059=p059 := StagedExprCompile.compile_plus e059 e057 e058 p057 p058 p059 rfl h057 h058 step059
#print axioms h059
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
