/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode043
import Proofs.RadenkovicGutmanD8Long00CompositionalNode066
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e071 : NestedArithmetic.Expr 3 := .times e043 e066
noncomputable def p071 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-192],[0,-192,96]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-1728,-2880],[-1728,-9792,1424],[-2880,1424,24]],[[0,0,0],[0,0,0],[0,0]],[[-44064,-121392,-9552],[-121392,-25104,6304],[-9552,6304]],[[0,0,0],[0,0,0],[0,0]],[[-1490184,-926352,9352],[-926352,72064,7744],[9352,7744]],[[0,0,0],[0,0,0],[0,0]],[[-14414544,-3047536,88480],[-3047536,386736,3760],[88480,3760]],[[0,0,0],[0,0,0],[0,0]],[[-71821560,-5114128,174224],[-5114128,686880,752],[174224,752]],[[0,0,0],[0,0,0],[0,0]],[[-221720176,-3492192,173376],[-3492192,649152,48],[173376,48]],[[0,0,0],[0,0],[0]],[[-460837544,2795728,99424],[2795728,361248],[99424]],[[0,0,0],[0,0],[0]],[[-670436064,8988208,33760],[8988208,120880],[33760]],[[0,0,0],[0,0],[0]],[[-688643056,10122640,6576],[10122640,23584],[6576]],[[0,0,0],[0,0],[0]],[[-484530096,6857456,656],[6857456,2416],[656]],[[0,0,0],[0,0],[0]],[[-202605856,3073152,24],[3073152,96],[24]],[[0,0],[0]],[[-8057824,929424],[929424]],[[0,0],[0]],[[55462976,186624],[186624]],[[0,0],[0]],[[44374960,23584],[23584]],[[0,0],[0]],[[20122712,1664],[1664]],[[0,0],[0]],[[6150304,48],[48]],[[0]],[[1309136]],[[0]],[[191376]],[[0]],[[18232]],[[0]],[[1008]],[[0]],[[24]]]
theorem step071 : p071=NestedArithmetic.mul p043 p066 := by decide +kernel
#print axioms step071
theorem h071 : NestedArithmetic.compile e071=p071 := StagedExprCompile.compile_times e071 e043 e066 p043 p066 p071 rfl h043 h066 step071
#print axioms h071
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
