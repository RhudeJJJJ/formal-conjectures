/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD2Long00CompositionalNode028
import Proofs.RadenkovicGutmanD2Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e054 : NestedArithmetic.Expr 3 := .plus e028 e053
noncomputable def p054 : NestedHorner.Poly 3 := [[[],[]],[[0,3],[3]],[[0,0],[0]],[[45,13],[13]],[[0,0],[0]],[[300,16],[16]],[[0,0],[0]],[[779,7],[7]],[[0,0],[0]],[[1056,1],[1]],[[0]],[[828]],[[0]],[[388]],[[0]],[[107]],[[0]],[[16]],[[0]],[[1]]]
theorem step054 : p054=NestedHorner.add p028 p053 := by decide +kernel
#print axioms step054
theorem h054 : NestedArithmetic.compile e054=p054 := StagedExprCompile.compile_plus e054 e028 e053 p028 p053 p054 rfl h028 h053 step054
#print axioms h054
end Gebendorfer.RadenkovicGutman.FixedDegree02Long00Compositional
