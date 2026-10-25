/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode075
import Proofs.RadenkovicGutmanD36Long00CompositionalNode077
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e078 : NestedArithmetic.Expr 3 := .plus e075 e077
noncomputable def p078 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1296]],[[0,0],[0,0,0],[0,0]],[[0,0,11664],[0,23328,23328],[11664,23328]],[[0,0,0],[0,0,0],[0,0]],[[-104976,384912,206064],[384912,622080,62208],[206064,62208]],[[0,0,0],[0,0,0],[0,0]],[[1329696,6193584,903312],[6193584,2926368,57024],[903312,57024]],[[0,0,0],[0,0,0],[0,0]],[[37476432,35680176,1853280],[35680176,6225984,20736],[1853280,20736]],[[0,0,0],[0,0,0],[0,0]],[[288808416,109830816,2130624],[109830816,7371648,2592],[2130624,2592]],[[0,0,0],[0,0],[0]],[[1201701744,210318768,1472256],[210318768,5241024],[1472256]],[[0,0,0],[0,0],[0]],[[3222244800,269991792,623376],[269991792,2283552],[623376]],[[0,0,0],[0,0],[0]],[[6046734240,241807680,158112],[241807680,596160],[158112]],[[0,0,0],[0,0],[0]],[[8316973728,154134576,22032],[154134576,85536],[22032]],[[0,0,0],[0,0],[0]],[[8621212320,70317072,1296],[70317072,5184],[1296]],[[0,0],[0]],[[6847882560,22778496],[22778496]],[[0,0],[0]],[[4204910880,5112720],[5112720]],[[0,0],[0]],[[2000943648,755568],[755568]],[[0,0],[0]],[[735219504,66096],[66096]],[[0,0],[0]],[[206421696,2592],[2592]],[[0]],[[43428960]],[[0]],[[6622560]],[[0]],[[690768]],[[0]],[[44064]],[[0]],[[1296]]]
theorem step078 : p078=NestedHorner.add p075 p077 := by decide +kernel
#print axioms step078
theorem h078 : NestedArithmetic.compile e078=p078 := StagedExprCompile.compile_plus e078 e075 e077 p075 p077 p078 rfl h075 h077 step078
#print axioms h078
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
