/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode051
import Proofs.RadenkovicGutmanD19Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-1083],[0,-1083]],[[0,0,0],[0,0,0],[0,0]],[[0,9747,-16245],[9747,-48735,-4807],[-16245,-4807]],[[0,0,0],[0,0,0],[0,0]],[[146205,-322677,-125571],[-322677,-361152,-6270],[-125571,-6270]],[[0,0,0],[0,0,0],[0,0]],[[-843885,-3943260,-386954],[-3943260,-1066527,-3135],[-386954,-3135]],[[0,0,0],[0,0,0],[0,0]],[[-24858954,-18585629,-623789],[-18585629,-1658396,-627],[-623789,-627]],[[0,0,0],[0,0,0],[0,0]],[[-173285643,-49086576,-578930],[-49086576,-1496896,-38],[-578930,-38]],[[0,0,0],[0,0],[0]],[[-657916591,-82461805,-319827],[-82461805,-811186],[-319827]],[[0,0,0],[0,0],[0]],[[-1623388044,-93552694,-104538],[-93552694,-262447],[-104538]],[[0,0,0],[0,0],[0]],[[-2813573200,-73859061,-19095],[-73859061,-48032],[-19095]],[[0,0,0],[0,0],[0]],[[-3572581343,-41069963,-1653],[-41069963,-4275],[-1653]],[[0,0,0],[0,0],[0]],[[-3405958354,-16047514,-38],[-16047514,-114],[-38]],[[0,0],[0]],[[-2471825292,-4327706],[-4327706]],[[0,0],[0]],[[-1373840828,-773642],[-773642]],[[0,0],[0]],[[-584396129,-84512],[-84512]],[[0,0],[0]],[[-188815027,-4712],[-4712]],[[0,0],[0]],[[-45597720,-76],[-76]],[[0]],[[-8001660]],[[0]],[[-972325]],[[0]],[[-74993]],[[0]],[[-3059]],[[0]],[[-38]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
