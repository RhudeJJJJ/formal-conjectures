/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode165
import Proofs.RadenkovicGutmanD42Long00CompositionalNode172
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e173 : NestedArithmetic.Expr 3 := .plus e165 e172
noncomputable def p173 : NestedHorner.Poly 3 := [[[-80],[0]],[[0,0],[0]],[[-1108,0],[0,0]],[[0,0],[0,0]],[[-6148,0],[0,0]],[[0,0],[0,0]],[[-16976,0],[0,0]],[[0,0],[0,0]],[[-22084,0],[0,0]],[[0,0],[0,0]],[[-3504,-80],[-80,0]],[[0,0],[0,0]],[[26132,-598],[-598,0]],[[0,0],[0,0]],[[32608,-1466],[-1466,0]],[[0,0],[0,0]],[[16260,-1248],[-1248,0]],[[0,0],[0,0]],[[3060,-174],[-174,0]],[[0,0],[0,0]],[[0,126],[126,-80]]]
theorem step173 : p173=NestedHorner.add p165 p172 := by decide +kernel
#print axioms step173
theorem h173 : NestedArithmetic.compile e173=p173 := StagedExprCompile.compile_plus e173 e165 e172 p165 p172 p173 rfl h165 h172 step173
#print axioms h173
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
