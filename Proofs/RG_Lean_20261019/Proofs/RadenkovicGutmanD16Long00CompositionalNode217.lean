/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode034
import Proofs.RadenkovicGutmanD16Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-32],[0]],[[0,0],[0]],[[-480,0],[0]],[[0,0],[0]],[[-3008,0],[0]],[[0,0],[0]],[[-10208,0],[0]],[[0,0],[0]],[[-20352,0],[0]],[[0,0],[0]],[[-24224,-16],[-16]],[[0,0],[0]],[[-16704,-112],[-112]],[[0,0],[0]],[[-6048,-256],[-256]],[[0,0],[0]],[[-864,-208],[-208]],[[0,0],[0]],[[0,-48],[-48]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
