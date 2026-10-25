/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode095
import Proofs.RadenkovicGutmanD37Long00CompositionalNode105
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e106 : NestedArithmetic.Expr 3 := .plus e095 e105
noncomputable def p106 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,0,0],[0,-2664,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-23976,-23976,0],[-23976,-23088,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-631368,-271728,0],[-271728,-78440,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6233760,-1318680,0],[-1318680,-135568,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-33593928,-3631920,0],[-3631920,-131424,0],[0,0]],[[0,0,0],[0,0],[0]],[[-114806264,-6349496,0],[-6349496,-74000],[0]],[[0,0,0],[0,0],[0]],[[-269205488,-7453280,0],[-7453280,-23976],[0]],[[0,0,0],[0,0],[0]],[[-453911264,-6046096,0],[-6046096,-4144],[0]],[[0,0,0],[0,0],[0]],[[-566775768,-3427680,0],[-3427680,-296],[0]],[[0,0,0],[0,0],[0]],[[-533850800,-1353016,0],[-1353016,0],[0]],[[0,0],[0]],[[-383347824,-364080],[-364080]],[[0,0],[0]],[[-210723584,-63640],[-63640]],[[0,0],[0]],[[-88483576,-6512],[-6512]],[[0,0],[0]],[[-28124440,-296],[-296]],[[0,0],[0]],[[-6644016,0],[0]],[[0]],[[-1129536]],[[0]],[[-130536]],[[0]],[[-9176]],[[0]],[[-296]],[[0]],[[0]]]
theorem step106 : p106=NestedHorner.add p095 p105 := by decide +kernel
#print axioms step106
theorem h106 : NestedArithmetic.compile e106=p106 := StagedExprCompile.compile_plus e106 e095 e105 p095 p105 p106 rfl h095 h105 step106
#print axioms h106
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
