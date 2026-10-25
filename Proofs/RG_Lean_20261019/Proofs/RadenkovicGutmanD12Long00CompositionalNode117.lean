/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode112
import Proofs.RadenkovicGutmanD12Long00CompositionalNode116
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e117 : NestedArithmetic.Expr 3 := .plus e112 e116
noncomputable def p117 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,288],[0,288,448]],[[0,0,0],[0,0,0],[0,0,0]],[[0,2592,7776],[2592,10656,9600],[7776,9600,4]],[[0,0,0],[0,0,0],[0,0]],[[106272,202176,101952],[202176,230664,24360],[101952,24360]],[[0,0,0],[0,0,0],[0,0]],[[3094308,2708424,414756],[2708424,1057568,22112],[414756,22112]],[[0,0,0],[0,0,0],[0,0]],[[34459128,14796312,823776],[14796312,2256648,8112],[823776,8112]],[[0,0,0],[0,0,0],[0,0]],[[203900844,44743224,930960],[44743224,2718736,1056],[930960,1056]],[[0,0,0],[0,0,0],[0,0]],[[751744840,85474592,637408],[85474592,1985184,8],[637408,8]],[[0,0,0],[0,0],[0]],[[1886851700,110391256,269048],[110391256,894160],[269048]],[[0,0,0],[0,0],[0]],[[3401799248,99997368,68512],[99997368,242888],[68512]],[[0,0,0],[0,0],[0]],[[4558094936,64709904,9712],[64709904,36688],[9712]],[[0,0,0],[0,0],[0]],[[4639754696,30059232,608],[30059232,2440],[608]],[[0,0,0],[0,0],[0]],[[3637130688,9943864,4],[9943864,16],[4]],[[0,0],[0]],[[2211641856,2287784],[2287784]],[[0,0],[0]],[[1044925536,348760],[348760]],[[0,0],[0]],[[382093848,31936],[31936]],[[0,0],[0]],[[107019796,1384],[1384]],[[0,0],[0]],[[22528944,8],[8]],[[0]],[[3452536]],[[0]],[[364728]],[[0]],[[23988]],[[0]],[[776]],[[0]],[[4]]]
theorem step117 : p117=NestedHorner.add p112 p116 := by decide +kernel
#print axioms step117
theorem h117 : NestedArithmetic.compile e117=p117 := StagedExprCompile.compile_plus e117 e112 e116 p112 p116 p117 rfl h112 h116 step117
#print axioms h117
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
