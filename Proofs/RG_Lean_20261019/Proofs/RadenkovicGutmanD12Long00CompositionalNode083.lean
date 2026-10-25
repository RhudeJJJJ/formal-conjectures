/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode070
import Proofs.RadenkovicGutmanD12Long00CompositionalNode082
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e083 : NestedArithmetic.Expr 3 := .plus e070 e082
noncomputable def p083 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,288],[0,288,448]],[[0,0,0],[0,0,0],[0,0,0]],[[0,2592,7776],[2592,19296,9600],[7776,9600,4]],[[0,0,0],[0,0,0],[0,0]],[[-2592,264384,101952],[264384,305112,24360],[101952,24360]],[[0,0,0],[0,0,0],[0,0]],[[1623348,3383640,414756],[3383640,1308224,22112],[414756,22112]],[[0,0,0],[0,0,0],[0,0]],[[25181064,17904120,823776],[17904120,2683608,8112],[823776,8112]],[[0,0,0],[0,0,0],[0,0]],[[166964268,52777704,930960],[52777704,3122992,1056],[930960,1056]],[[0,0,0],[0,0,0],[0,0]],[[647116696,98519936,637408],[98519936,2203872,8],[637408,8]],[[0,0,0],[0,0],[0]],[[1664607332,124443400,269048],[124443400,959920],[269048]],[[0,0,0],[0,0],[0]],[[3040184624,110294520,68512],[110294520,252440],[68512]],[[0,0,0],[0,0],[0]],[[4103509208,69857520,9712],[69857520,36976],[9712]],[[0,0,0],[0,0],[0]],[[4196297720,31774752,608],[31774752,2392],[608]],[[0,0,0],[0,0],[0]],[[3300485280,10298152,4],[10298152,16],[4]],[[0,0],[0]],[[2012544096,2322824],[2322824]],[[0,0],[0]],[[953334048,347464],[347464]],[[0,0],[0]],[[349501128,31264],[31264]],[[0,0],[0]],[[98149444,1336],[1336]],[[0,0],[0]],[[20718864,8],[8]],[[0]],[[3184696]],[[0]],[[337608]],[[0]],[[22308]],[[0]],[[728]],[[0]],[[4]]]
theorem step083 : p083=NestedHorner.add p070 p082 := by decide +kernel
#print axioms step083
theorem h083 : NestedArithmetic.compile e083=p083 := StagedExprCompile.compile_plus e083 e070 e082 p070 p082 p083 rfl h070 h082 step083
#print axioms h083
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
