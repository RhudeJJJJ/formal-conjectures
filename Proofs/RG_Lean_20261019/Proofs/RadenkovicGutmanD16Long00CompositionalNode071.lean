/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD16Long00CompositionalNode043
import Proofs.RadenkovicGutmanD16Long00CompositionalNode066
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e071 : NestedArithmetic.Expr 3 := .times e043 e066
noncomputable def p071 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-768],[0,-768,448]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-6912,-11520],[-6912,-38016,7328],[-11520,7328,56]],[[0,0,0],[0,0,0],[0,0]],[[-171072,-470880,-28704],[-470880,-53136,29648],[-28704,29648]],[[0,0,0],[0,0,0],[0,0]],[[-5703048,-3328272,92056],[-3328272,534528,34432],[92056,34432]],[[0,0,0],[0,0,0],[0,0]],[[-53433648,-9565168,482368],[-9565168,2098160,15424],[482368,15424]],[[0,0,0],[0,0,0],[0,0]],[[-255824856,-11335728,855936],[-11335728,3403872,2656],[855936,2656]],[[0,0,0],[0,0,0],[0,0]],[[-751437840,5107520,803968],[5107520,3034944,112],[803968,112]],[[0,0,0],[0,0],[0]],[[-1462344296,37288912,438896],[37288912,1600160],[438896]],[[0,0,0],[0,0],[0]],[[-1931760928,60274576,140992],[60274576,502640],[140992]],[[0,0,0],[0,0],[0]],[[-1678403952,56122688,25408],[56122688,89760],[25408]],[[0,0,0],[0,0],[0]],[[-784265296,34285024,2208],[34285024,7920],[2208]],[[0,0,0],[0,0],[0]],[[126798016,14244528,56],[14244528,224],[56]],[[0,0],[0]],[[547355584,4023536],[4023536]],[[0,0],[0]],[[493716352,750576],[750576]],[[0,0],[0]],[[272782544,86336],[86336]],[[0,0],[0]],[[104595672,5264],[5264]],[[0,0],[0]],[[28655776,112],[112]],[[0]],[[5576144]],[[0]],[[745936]],[[0]],[[64024]],[[0]],[[3056]],[[0]],[[56]]]
theorem step071 : p071=NestedArithmetic.mul p043 p066 := by decide +kernel
#print axioms step071
theorem h071 : NestedArithmetic.compile e071=p071 := StagedExprCompile.compile_times e071 e043 e066 p043 p066 p071 rfl h043 h066 step071
#print axioms h071
end Gebendorfer.RadenkovicGutman.FixedDegree16Long00Compositional
