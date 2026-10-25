/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode065
import Proofs.RadenkovicGutmanD20Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-20]],[[0,0],[0,0]],[[-180,-300],[-300,-2]],[[0,0],[0]],[[-4998,-1018],[-1018]],[[0,0],[0]],[[-26258,-1128],[-1128]],[[0,0],[0]],[[-61154,-484],[-484]],[[0,0],[0]],[[-77980,-76],[-76]],[[0,0],[0]],[[-59128,-2],[-2]],[[0]],[[-27412]],[[0]],[[-7682]],[[0]],[[-1224]],[[0]],[[-94]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
