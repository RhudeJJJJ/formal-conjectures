/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD17Long00CompositionalNode065
import Proofs.RadenkovicGutmanD17Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e066 : NestedArithmetic.Expr 3 := .times e065 e064
noncomputable def p066 : NestedHorner.Poly 3 := [[[0],[0,-17]],[[0,0],[0,0]],[[-153,-255],[-255,-2]],[[0,0],[0]],[[-4251,-868],[-868]],[[0,0],[0]],[[-22367,-966],[-966]],[[0,0],[0]],[[-52190,-418],[-418]],[[0,0],[0]],[[-66712,-67],[-67]],[[0,0],[0]],[[-50752,-2],[-2]],[[0]],[[-23641]],[[0]],[[-6674]],[[0]],[[-1077]],[[0]],[[-85]],[[0]],[[-2]]]
theorem step066 : p066=NestedArithmetic.mul p065 p064 := by decide +kernel
#print axioms step066
theorem h066 : NestedArithmetic.compile e066=p066 := StagedExprCompile.compile_times e066 e065 e064 p065 p064 p066 rfl h065 h064 step066
#print axioms h066
end Gebendorfer.RadenkovicGutman.FixedDegree17Long00Compositional
