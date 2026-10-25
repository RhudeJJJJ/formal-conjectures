/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode041
import Proofs.RadenkovicGutmanD42Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,126],[126,-80]],[[0,0],[0]],[[3060,-174],[-174]],[[0,0],[0]],[[16260,-1248],[-1248]],[[0,0],[0]],[[32608,-1466],[-1466]],[[0,0],[0]],[[26132,-598],[-598]],[[0,0],[0]],[[-3504,-80],[-80]],[[0]],[[-22084]],[[0]],[[-16976]],[[0]],[[-6148]],[[0]],[[-1108]],[[0]],[[-80]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
