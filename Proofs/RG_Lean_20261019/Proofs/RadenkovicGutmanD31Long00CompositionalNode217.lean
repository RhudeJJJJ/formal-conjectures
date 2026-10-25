/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode034
import Proofs.RadenkovicGutmanD31Long00CompositionalNode170
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e217 : NestedArithmetic.Expr 3 := .times e034 e170
noncomputable def p217 : NestedHorner.Poly 3 := [[[-62],[0]],[[0,0],[0]],[[-930,0],[0]],[[0,0],[0]],[[-5828,0],[0]],[[0,0],[0]],[[-19778,0],[0]],[[0,0],[0]],[[-39432,0],[0]],[[0,0],[0]],[[-46934,-31],[-31]],[[0,0],[0]],[[-32364,-217],[-217]],[[0,0],[0]],[[-11718,-496],[-496]],[[0,0],[0]],[[-1674,-403],[-403]],[[0,0],[0]],[[0,-93],[-93]]]
theorem step217 : p217=NestedArithmetic.mul p034 p170 := by decide +kernel
#print axioms step217
theorem h217 : NestedArithmetic.compile e217=p217 := StagedExprCompile.compile_times e217 e034 e170 p034 p170 p217 rfl h034 h170 step217
#print axioms h217
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
