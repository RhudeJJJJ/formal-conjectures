/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD4Long00CompositionalNode042
import Proofs.RadenkovicGutmanD4Long00CompositionalNode056
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .times e042 e056
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-144],[0,-288,48],[-144,48]],[[0,0,0],[0,0,0],[0,0]],[[0,-6048,-816],[-6048,-912,208],[-816,208]],[[0,0,0],[0,0,0],[0,0]],[[-58320,-59616,-1216],[-59616,2368,256],[-1216,256]],[[0,0,0],[0,0,0],[0,0]],[[-771120,-249552,1024],[-249552,14512,112],[1024,112]],[[0,0,0],[0,0,0],[0,0]],[[-4571424,-580976,5008],[-580976,26912,16],[5008,16]],[[0,0,0],[0,0],[0]],[[-16120080,-817456,6176],[-817456,25600],[6176]],[[0,0,0],[0,0],[0]],[[-37789392,-687872,3808],[-687872,13824],[3808]],[[0,0,0],[0,0],[0]],[[-62291872,-280928,1280],[-280928,4272],[1280]],[[0,0,0],[0,0],[0]],[[-74379168,50368,224],[50368,704],[224]],[[0,0,0],[0,0],[0]],[[-65149424,136768,16],[136768,48],[16]],[[0,0],[0]],[[-41728192,84416],[84416]],[[0,0],[0]],[[-19036960,28720],[28720]],[[0,0],[0]],[[-5693600,5808],[5808]],[[0,0],[0]],[[-766704,656],[656]],[[0,0],[0]],[[182064,32],[32]],[[0]],[[127200]],[[0]],[[33760]],[[0]],[[5104]],[[0]],[[432]],[[0]],[[16]]]
theorem step099 : p099=NestedArithmetic.mul p042 p056 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_times e099 e042 e056 p042 p056 p099 rfl h042 h056 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree04Long00Compositional
