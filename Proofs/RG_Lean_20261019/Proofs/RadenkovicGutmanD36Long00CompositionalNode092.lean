/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode089
import Proofs.RadenkovicGutmanD36Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,7776],[0,7776,-2448]],[[0,0,0],[0,0,0],[0,0]],[[0,0,93312],[0,314928,-10152],[93312,-10152]],[[0,0,0],[0,0,0],[0,0]],[[303264,2556360,495720],[2556360,1477440,-75096],[495720,-75096]],[[0,0,0],[0,0,0],[0,0]],[[21982752,22192704,995976],[22192704,2266704,-88416],[995976,-88416]],[[0,0,0],[0,0,0],[0,0]],[[238120560,83870640,807408],[83870640,261792,-36072],[807408,-36072]],[[0,0,0],[0,0,0],[0,0]],[[1242451440,180079920,-83736],[180079920,-3212064,-4824],[-83736,-4824]],[[0,0,0],[0,0],[0]],[[3953424096,239537952,-648288],[239537952,-4213152],[-648288]],[[0,0,0],[0,0],[0]],[[8477188560,199036224,-502632],[199036224,-2535408],[-502632]],[[0,0,0],[0,0],[0]],[[12892747104,93199536,-182448],[93199536,-820512],[-182448]],[[0,0,0],[0,0],[0]],[[14279721552,9168840,-32904],[9168840,-138096],[-32904]],[[0,0,0],[0,0],[0]],[[11624666832,-17816328,-2376],[-17816328,-9504],[-2376]],[[0,0],[0]],[[6896649456,-12763800],[-12763800]],[[0,0],[0]],[[2868813360,-4427424],[-4427424]],[[0,0],[0]],[[735030288,-886680],[-886680]],[[0,0],[0]],[[42946560,-98208],[-98208]],[[0,0],[0]],[[-51014736,-4680],[-4680]],[[0]],[[-23936256]],[[0]],[[-5662800]],[[0]],[[-801360]],[[0]],[[-64656]],[[0]],[[-2304]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
