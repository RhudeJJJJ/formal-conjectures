/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode089
import Proofs.RadenkovicGutmanD11Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,726],[0,726,-198]],[[0,0,0],[0,0,0],[0,0]],[[0,0,8712],[0,29403,-352],[8712,-352]],[[0,0,0],[0,0,0],[0,0]],[[25839,239085,49170],[239085,149490,-5346],[49170,-5346]],[[0,0,0],[0,0,0],[0,0]],[[2016927,2133054,109076],[2133054,275979,-6666],[109076,-6666]],[[0,0,0],[0,0,0],[0,0]],[[22283910,8324415,113058],[8324415,175142,-2772],[113058,-2772]],[[0,0,0],[0,0,0],[0,0]],[[118260615,18634220,40414],[18634220,-106964,-374],[40414,-374]],[[0,0,0],[0,0],[0]],[[382998121,26341777,-23738],[26341777,-246202],[-23738]],[[0,0,0],[0,0],[0]],[[837980110,24286174,-29832],[24286174,-168333],[-29832]],[[0,0,0],[0,0],[0]],[[1306358504,14345386,-12298],[14345386,-57662],[-12298]],[[0,0,0],[0,0],[0]],[[1494372077,4804140,-2354],[4804140,-10021],[-2354]],[[0,0,0],[0,0],[0]],[[1272719382,303347,-176],[303347,-704],[-176]],[[0,0],[0]],[[808910806,-498850],[-498850]],[[0,0],[0]],[[379193760,-244849],[-244849]],[[0,0],[0]],[[126452513,-55880],[-55880]],[[0,0],[0]],[[27065885,-6633],[-6633]],[[0,0],[0]],[[2227214,-330],[-330]],[[0]],[[-653356]],[[0]],[[-270325]],[[0]],[[-46035]],[[0]],[[-4081]],[[0]],[[-154]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
