/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode028
import Proofs.RadenkovicGutmanD4Long00CompositionalNode054
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e055 : NestedArithmetic.Expr 3 := .plus e028 e054
noncomputable def p055 : NestedHorner.Poly 3 := [[[],[]],[[0,3],[3]],[[0,0],[0]],[[45,13],[13]],[[0,0],[0]],[[300,16],[16]],[[0,0],[0]],[[779,7],[7]],[[0,0],[0]],[[1056,1],[1]],[[0]],[[828]],[[0]],[[388]],[[0]],[[107]],[[0]],[[16]],[[0]],[[1]]]
theorem step055 : p055=NestedHorner.add p028 p054 := by decide +kernel
#print axioms step055
theorem h055 : NestedArithmetic.compile e055=p055 := StagedExprCompile.compile_plus e055 e028 e054 p028 p054 p055 rfl h028 h054 step055
#print axioms h055
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
