/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode065
import Proofs.RadenkovicGutmanD36Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-36]],[[0,0],[0,0]],[[-324,-540],[-540,-2]],[[0,0],[0]],[[-8982,-1818],[-1818]],[[0,0],[0]],[[-47010,-1992],[-1992]],[[0,0],[0]],[[-108962,-836],[-836]],[[0,0],[0]],[[-138076,-124],[-124]],[[0,0],[0]],[[-103800,-2],[-2]],[[0]],[[-47524]],[[0]],[[-13058]],[[0]],[[-2008]],[[0]],[[-142]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
