/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode041
import Proofs.RadenkovicGutmanD21Long00CompositionalNode042
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e043 : NestedArithmetic.Expr 3 := .plus e041 e042
noncomputable def p043 : NestedHorner.Poly 3 := [[[0],[0]],[[0,63],[63,-38]],[[0,0],[0]],[[1548,-69],[-69]],[[0,0],[0]],[[8448,-576],[-576]],[[0,0],[0]],[[17698,-689],[-689]],[[0,0],[0]],[[15926,-283],[-283]],[[0,0],[0]],[[1536,-38],[-38]],[[0]],[[-8770]],[[0]],[[-7526]],[[0]],[[-2830]],[[0]],[[-520]],[[0]],[[-38]]]
theorem step043 : p043=NestedHorner.add p041 p042 := by decide +kernel
#print axioms step043
theorem h043 : NestedArithmetic.compile e043=p043 := StagedExprCompile.compile_plus e043 e041 e042 p041 p042 p043 rfl h041 h042 step043
#print axioms h043
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
