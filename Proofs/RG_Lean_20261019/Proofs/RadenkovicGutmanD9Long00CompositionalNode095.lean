/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode093
import Proofs.RadenkovicGutmanD9Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,81]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-729],[0,-1458,2322],[-729,2322,18]],[[0,0,0],[0,0,0],[0,0]],[[-6561,-25029,8019],[-25029,43254,7956],[8019,7956]],[[0,0,0],[0,0,0],[0,0]],[[-316386,33291,69417],[33291,307962,9036],[69417,9036]],[[0,0,0],[0,0,0],[0,0]],[[-1968057,1496313,199746],[1496313,830250,4104],[199746,4104]],[[0,0,0],[0,0,0],[0,0]],[[-1096416,7665480,296748],[7665480,1184724,738],[296748,738]],[[0,0,0],[0,0,0],[0,0]],[[33018381,20021229,256284],[20021229,993708,36],[256284,36]],[[0,0,0],[0,0],[0]],[[172003968,32560083,133659],[32560083,507258],[133659]],[[0,0,0],[0,0],[0]],[[468565254,35620416,41886],[35620416,156690],[41886]],[[0,0,0],[0,0],[0]],[[842823954,27171045,7479],[27171045,27810],[7479]],[[0,0,0],[0,0],[0]],[[1084016304,14662251,657],[14662251,2466],[657]],[[0,0,0],[0,0],[0]],[[1035571824,5592582,18],[5592582,72],[18]],[[0,0],[0]],[[749491362,1483515],[1483515]],[[0,0],[0]],[[414737982,263727],[263727]],[[0,0],[0]],[[175694805,29205],[29205]],[[0,0],[0]],[[56636856,1728],[1728]],[[0,0],[0]],[[13694346,36],[36]],[[0]],[[2420478]],[[0]],[[299367]],[[0]],[[23994]],[[0]],[[1071]],[[0]],[[18]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
