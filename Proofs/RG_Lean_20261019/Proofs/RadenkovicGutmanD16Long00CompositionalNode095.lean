/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode093
import Proofs.RadenkovicGutmanD16Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,256]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-2304],[0,-4608,7488],[-2304,7488,32]],[[0,0,0],[0,0,0],[0,0]],[[-20736,-77760,26688],[-77760,142080,25344],[26688,25344]],[[0,0,0],[0,0,0],[0,0]],[[-973728,158976,226784],[158976,1002880,28160],[226784,28160]],[[0,0,0],[0,0,0],[0,0]],[[-5588352,5140800,646528],[5140800,2684928,12224],[646528,12224]],[[0,0,0],[0,0,0],[0,0]],[[1974624,25709184,951360],[25709184,3798272,1984],[951360,1984]],[[0,0,0],[0,0,0],[0,0]],[[129746432,66379520,811776],[66379520,3147776,64],[811776,64]],[[0,0,0],[0,0],[0]],[[618878816,107000064,416256],[107000064,1578496],[416256]],[[0,0,0],[0,0],[0]],[[1634217728,116054336,127104],[116054336,474112],[127104]],[[0,0,0],[0,0],[0]],[[2888071872,87686080,21696],[87686080,80128],[21696]],[[0,0,0],[0,0],[0]],[[3667534080,46778048,1728],[46778048,6400],[1728]],[[0,0,0],[0,0],[0]],[[3466122240,17580992,32],[17580992,128],[32]],[[0,0],[0]],[[2483149568,4569920],[4569920]],[[0,0],[0]],[[1359669760,788160],[788160]],[[0,0],[0]],[[569296384,82944],[82944]],[[0,0],[0]],[[180998240,4416],[4416]],[[0,0],[0]],[[43010304,64],[64]],[[0]],[[7426752]],[[0]],[[887808]],[[0]],[[67296]],[[0]],[[2688]],[[0]],[[32]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
