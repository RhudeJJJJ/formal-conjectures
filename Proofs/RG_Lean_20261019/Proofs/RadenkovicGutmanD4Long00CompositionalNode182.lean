/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode178
import Proofs.RadenkovicGutmanD4Long00CompositionalNode181
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e182 : NestedArithmetic.Expr 3 := .plus e178 e181
noncomputable def p182 : NestedHorner.Poly 3 := [[[1],[]],[[0,0],[0]],[[16,0],[0]],[[0,0],[0]],[[107,0],[0]],[[0,0],[0]],[[388,0],[0]],[[0,0],[0]],[[828,0],[0]],[[0,0],[0]],[[1056,1],[1]],[[0,0],[0]],[[779,7],[7]],[[0,0],[0]],[[300,16],[16]],[[0,0],[0]],[[45,13],[13]],[[0,0],[0]],[[0,3],[3]]]
theorem step182 : p182=NestedHorner.add p178 p181 := by decide +kernel
#print axioms step182
theorem h182 : NestedArithmetic.compile e182=p182 := StagedExprCompile.compile_plus e182 e178 e181 p178 p181 p182 rfl h178 h181 step182
#print axioms h182
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
