/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode179
import Proofs.RadenkovicGutmanD45Long00CompositionalNode182
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e183 : NestedArithmetic.Expr 3 := .plus e179 e182
noncomputable def p183 : NestedHorner.Poly 3 := [[[1],[]],[[0,0],[0]],[[16,0],[0]],[[0,0],[0]],[[107,0],[0]],[[0,0],[0]],[[388,0],[0]],[[0,0],[0]],[[828,0],[0]],[[0,0],[0]],[[1056,1],[1]],[[0,0],[0]],[[779,7],[7]],[[0,0],[0]],[[300,16],[16]],[[0,0],[0]],[[45,13],[13]],[[0,0],[0]],[[0,3],[3]]]
theorem step183 : p183=NestedHorner.add p179 p182 := by decide +kernel
#print axioms step183
theorem h183 : NestedArithmetic.compile e183=p183 := StagedExprCompile.compile_plus e183 e179 e182 p179 p182 p183 rfl h179 h182 step183
#print axioms h183
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
