/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD29Long00CompositionalNode051
import Proofs.RadenkovicGutmanD29Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-2523],[0,-2523]],[[0,0,0],[0,0,0],[0,0]],[[0,22707,-37845],[22707,-113535,-11107],[-37845,-11107]],[[0,0,0],[0,0,0],[0,0]],[[340605,-750897,-291711],[-750897,-838332,-14210],[-291711,-14210]],[[0,0,0],[0,0,0],[0,0]],[[-1953585,-9155880,-895694],[-9155880,-2463927,-6815],[-895694,-6815]],[[0,0,0],[0,0,0],[0,0]],[[-57611574,-43051109,-1437269],[-43051109,-3807816,-1247],[-1437269,-1247]],[[0,0,0],[0,0,0],[0,0]],[[-401065563,-113402876,-1325590],[-113402876,-3408776,-58],[-1325590,-58]],[[0,0,0],[0,0],[0]],[[-1520290171,-189940285,-725667],[-189940285,-1825666],[-725667]],[[0,0,0],[0,0],[0]],[[-3744627784,-214736474,-233798],[-214736474,-580087],[-233798]],[[0,0,0],[0,0],[0]],[[-6477397080,-168818541,-41615],[-168818541,-102892],[-41615]],[[0,0,0],[0,0],[0]],[[-8207042543,-93374983,-3393],[-93374983,-8555],[-3393]],[[0,0,0],[0,0],[0]],[[-7805150654,-36229294,-58],[-36229294,-174],[-58]],[[0,0],[0]],[[-5648418972,-9674226],[-9674226]],[[0,0],[0]],[[-3128789468,-1703402],[-1703402]],[[0,0],[0]],[[-1325384129,-181192],[-181192]],[[0,0],[0]],[[-425961367,-9512],[-9512]],[[0,0],[0]],[[-102143220,-116],[-116]],[[0]],[[-17746260]],[[0]],[[-2123525]],[[0]],[[-159413]],[[0]],[[-6119]],[[0]],[[-58]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree29Long00Compositional
