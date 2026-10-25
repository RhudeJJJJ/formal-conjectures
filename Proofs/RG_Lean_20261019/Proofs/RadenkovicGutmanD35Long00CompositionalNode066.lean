/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode065
import Proofs.RadenkovicGutmanD35Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-35]],[[0,0],[0,0]],[[-315,-525],[-525,-2]],[[0,0],[0]],[[-8733,-1768],[-1768]],[[0,0],[0]],[[-45713,-1938],[-1938]],[[0,0],[0]],[[-105974,-814],[-814]],[[0,0],[0]],[[-134320,-121],[-121]],[[0,0],[0]],[[-101008,-2],[-2]],[[0]],[[-46267]],[[0]],[[-12722]],[[0]],[[-1959]],[[0]],[[-139]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
