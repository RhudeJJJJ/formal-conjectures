/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode035
import Proofs.RadenkovicGutmanD14Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-588],[0,-588]],[[0,0,0],[0,0,0],[0,0]],[[0,-5292,-5292],[-5292,-21168,-2548],[-5292,-2548]],[[0,0,0],[0,0,0],[0,0]],[[-95256,-211680,-37044],[-211680,-148176,-3136],[-37044,-3136]],[[0,0,0],[0,0,0],[0,0]],[[-2349648,-1764000,-102312],[-1764000,-409248,-1372],[-102312,-1372]],[[0,0,0],[0,0,0],[0,0]],[[-20998656,-6980344,-148372],[-6980344,-593488,-196],[-148372,-196]],[[0,0,0],[0,0],[0]],[[-101980368,-16312296,-124656],[-16312296,-498624],[-124656]],[[0,0,0],[0,0],[0]],[[-315394968,-24799488,-62524],[-24799488,-250096],[-62524]],[[0,0,0],[0,0],[0]],[[-674033024,-25779880,-18424],[-25779880,-73696],[-18424]],[[0,0,0],[0,0],[0]],[[-1043985376,-18791892,-2940],[-18791892,-11760],[-2940]],[[0,0,0],[0,0],[0]],[[-1206813944,-9689652,-196],[-9689652,-784],[-196]],[[0,0],[0]],[[-1060053064,-3514084],[-3514084]],[[0,0],[0]],[[-714618744,-876120],[-876120]],[[0,0],[0]],[[-370988800,-142884],[-142884]],[[0,0],[0]],[[-147900032,-13720],[-13720]],[[0,0],[0]],[[-44838920,-588],[-588]],[[0]],[[-10144176]],[[0]],[[-1657376]],[[0]],[[-184632]],[[0]],[[-12544]],[[0]],[[-392]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
