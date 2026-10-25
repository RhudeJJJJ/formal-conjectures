/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode067
import Proofs.RadenkovicGutmanD11Long00CompositionalNode069
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e070 : NestedArithmetic.Expr 3 := .plus e067 e069
noncomputable def p070 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,121]],[[0,0],[0,0,0],[0,0,0]],[[0,0,1089],[0,2178,2442],[1089,2442,368]],[[0,0,0],[0,0,0],[0,0,0]],[[-9801,38313,25971],[38313,75000,13840],[25971,13840,4]],[[0,0,0],[0,0,0],[0,0]],[[125442,807759,170905],[807759,532430,25612],[170905,25612]],[[0,0,0],[0,0,0],[0,0]],[[4945725,6227091,523158],[6227091,1684308,20344],[523158,20344]],[[0,0,0],[0,0,0],[0,0]],[[48826050,25483542,892572],[25483542,2944004,7010],[892572,7010]],[[0,0,0],[0,0,0],[0,0]],[[255783731,64382287,920424],[64382287,3110980,888],[920424,888]],[[0,0,0],[0,0,0],[0,0]],[[854610072,108574451,594089],[108574451,2062770,8],[594089,8]],[[0,0,0],[0,0],[0]],[[1984746938,127758396,241054],[127758396,861756],[241054]],[[0,0,0],[0,0],[0]],[[3365174066,107555419,59769],[107555419,220350],[59769]],[[0,0,0],[0,0],[0]],[[4294252570,65560701,8333],[65560701,31716],[8333]],[[0,0,0],[0,0],[0]],[[4204286432,28966108,520],[28966108,2044],[520]],[[0,0,0],[0,0],[0]],[[3194811994,9181797,4],[9181797,16],[4]],[[0,0],[0]],[[1894977986,2036555],[2036555]],[[0,0],[0]],[[877739747,301011],[301011]],[[0,0],[0]],[[315958336,26910],[26910]],[[0,0],[0]],[[87418358,1156],[1156]],[[0,0],[0]],[[18233934,8],[8]],[[0]],[[2776941]],[[0]],[[292550]],[[0]],[[19297]],[[0]],[[636]],[[0]],[[4]]]
theorem step070 : p070=NestedHorner.add p067 p069 := by decide +kernel
#print axioms step070
theorem h070 : NestedArithmetic.compile e070=p070 := StagedExprCompile.compile_plus e070 e067 e069 p067 p069 p070 rfl h067 h069 step070
#print axioms h070
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
