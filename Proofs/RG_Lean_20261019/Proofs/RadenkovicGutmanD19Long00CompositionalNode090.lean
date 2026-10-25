/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode035
import Proofs.RadenkovicGutmanD19Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e090 : NestedArithmetic.Expr 3 := .times e035 e064
noncomputable def p090 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-1083],[0,-1083]],[[0,0,0],[0,0,0],[0,0]],[[0,-9747,-16245],[-9747,-51984,-4807],[-16245,-4807]],[[0,0,0],[0,0,0],[0,0]],[[-175446,-605340,-125571],[-605340,-389652,-6270],[-125571,-6270]],[[0,0,0],[0,0,0],[0,0]],[[-6100596,-5687802,-386954],[-5687802,-1165156,-3135],[-386954,-3135]],[[0,0,0],[0,0,0],[0,0]],[[-63109260,-24654628,-623789],[-24654628,-1833804,-627],[-623789,-627]],[[0,0,0],[0,0,0],[0,0]],[[-338068368,-62407818,-578930],[-62407818,-1674584,-38],[-578930,-38]],[[0,0,0],[0,0],[0]],[[-1129770894,-102067202,-319827],[-102067202,-918308],[-319827]],[[0,0,0],[0,0],[0]],[[-2579533100,-113614908,-104538],[-113614908,-301188],[-104538]],[[0,0,0],[0,0],[0]],[[-4238386240,-88442929,-19095],[-88442929,-56164],[-19095]],[[0,0,0],[0,0],[0]],[[-5173384714,-48679881,-1653],[-48679881,-5168],[-1653]],[[0,0,0],[0,0],[0]],[[-4784144482,-18898673,-38],[-18898673,-152],[-38]],[[0,0],[0]],[[-3390071162,-5086224],[-5086224]],[[0,0],[0]],[[-1849528248,-913159],[-913159]],[[0,0],[0]],[[-775958708,-101346],[-101346]],[[0,0],[0]],[[-248460682,-5909],[-5909]],[[0,0],[0]],[[-59789200,-114],[-114]],[[0]],[[-10529648]],[[0]],[[-1298194]],[[0]],[[-103664]],[[0]],[[-4598]],[[0]],[[-76]]]
theorem step090 : p090=NestedArithmetic.mul p035 p064 := by decide +kernel
#print axioms step090
theorem h090 : NestedArithmetic.compile e090=p090 := StagedExprCompile.compile_times e090 e035 e064 p035 p064 p090 rfl h035 h064 step090
#print axioms h090
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
