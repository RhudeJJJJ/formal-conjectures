/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode043
import Proofs.RadenkovicGutmanD5Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,225],[0,450,-180],[225,-180,36]],[[0,0,0],[0,0,0],[0,0]],[[0,8505,330],[8505,-2742,-132],[330,-132]],[[0,0,0],[0,0,0],[0,0]],[[67716,51867,-1799],[51867,-21850,768],[-1799,768]],[[0,0,0],[0,0,0],[0,0]],[[643032,87939,-4318],[87939,-44942,1164],[-4318,1164]],[[0,0,0],[0,0,0],[0,0]],[[2332962,-110376,672],[-110376,-27756,516],[672,516]],[[0,0,0],[0,0,0],[0,0]],[[2831046,-658589,11290],[-658589,24668,72],[11290,72]],[[0,0,0],[0,0],[0]],[[-6953314,-1087913,14781],[-1087913,50574],[14781]],[[0,0,0],[0,0],[0]],[[-36302200,-805300,9110],[-805300,34282],[9110]],[[0,0,0],[0,0],[0]],[[-77123658,-30729,3013],[-30729,11750],[3013]],[[0,0,0],[0,0],[0]],[[-102045752,483857,516],[483857,2046],[516]],[[0,0,0],[0,0],[0]],[[-91695908,471360,36],[471360,144],[36]],[[0,0],[0]],[[-56493530,239345],[239345]],[[0,0],[0]],[[-22402150,74245],[74245]],[[0,0],[0]],[[-4006458,14155],[14155]],[[0,0],[0]],[[1204686,1530],[1530]],[[0,0],[0]],[[1142436,72],[72]],[[0]],[[418810]],[[0]],[[92300]],[[0]],[[12708]],[[0]],[[1014]],[[0]],[[36]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
