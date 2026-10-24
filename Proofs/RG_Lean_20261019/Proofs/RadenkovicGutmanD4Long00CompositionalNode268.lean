/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode172
import Proofs.RadenkovicGutmanD4Long00CompositionalNode216
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e268 : NestedArithmetic.Expr 3 := .times e172 e216
noncomputable def p268 : NestedHorner.Poly 3 := [[[16],[0],[0]],[[0,0],[0,0],[0]],[[432,0,0],[0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[5104,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[33760,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[127200,0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[182064,32,0],[32,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-766704,656,0],[656,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5693600,5808,0],[5808,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-19036960,28720,0],[28720,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-41728192,84416,0],[84416,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-65149424,136768,16],[136768,48,0],[16,0]],[[0,0,0],[0,0,0],[0,0]],[[-74379168,50368,224],[50368,704,0],[224,0]],[[0,0,0],[0,0,0],[0,0]],[[-62291872,-280928,1280],[-280928,4272,0],[1280,0]],[[0,0,0],[0,0,0],[0,0]],[[-37789392,-687872,3808],[-687872,13824,0],[3808,0]],[[0,0,0],[0,0,0],[0,0]],[[-16120080,-817456,6176],[-817456,25600,0],[6176,0]],[[0,0,0],[0,0,0],[0,0]],[[-4571424,-580976,5008],[-580976,26912,16],[5008,16]],[[0,0,0],[0,0,0],[0,0]],[[-771120,-249552,1024],[-249552,14512,112],[1024,112]],[[0,0,0],[0,0,0],[0,0]],[[-58320,-59616,-1216],[-59616,2368,256],[-1216,256]],[[0,0,0],[0,0,0],[0,0]],[[0,-6048,-816],[-6048,-912,208],[-816,208]],[[0,0,0],[0,0,0],[0,0]],[[0,0,-144],[0,-288,48],[-144,48]]]
theorem step268 : p268=NestedArithmetic.mul p172 p216 := by decide +kernel
#print axioms step268
theorem h268 : NestedArithmetic.compile e268=p268 := StagedExprCompile.compile_times e268 e172 e216 p172 p216 p268 rfl h172 h216 step268
#print axioms h268
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
