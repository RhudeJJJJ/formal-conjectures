/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode051
import Proofs.RadenkovicGutmanD31Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-2883],[0,-2883]],[[0,0,0],[0,0,0],[0,0]],[[0,25947,-43245],[25947,-129735,-12679],[-43245,-12679]],[[0,0,0],[0,0,0],[0,0]],[[389205,-857925,-333219],[-857925,-957528,-16182],[-333219,-16182]],[[0,0,0],[0,0,0],[0,0]],[[-2230605,-10458036,-1022690],[-10458036,-2812599,-7719],[-1022690,-7719]],[[0,0,0],[0,0,0],[0,0]],[[-65789874,-49159397,-1640117],[-49159397,-4343348,-1395],[-1640117,-1395]],[[0,0,0],[0,0,0],[0,0]],[[-457924467,-129450792,-1511498],[-129450792,-3884176,-62],[-1511498,-62]],[[0,0,0],[0,0],[0]],[[-1735476751,-216738949,-826491],[-216738949,-2077186],[-826491]],[[0,0,0],[0,0],[0]],[[-4273716420,-244927342,-265794],[-244927342,-658471],[-265794]],[[0,0,0],[0,0],[0]],[[-7390823584,-192452061,-47151],[-192452061,-116312],[-47151]],[[0,0,0],[0,0],[0]],[[-9361864871,-106375787,-3813],[-106375787,-9579],[-3813]],[[0,0,0],[0,0],[0]],[[-8900706298,-41236882,-62],[-41236882,-186],[-62]],[[0,0],[0]],[[-6438962508,-10997498],[-10997498]],[[0,0],[0]],[[-3565175708,-1932602],[-1932602]],[[0,0],[0]],[[-1509450233,-204848],[-204848]],[[0,0],[0]],[[-484792291,-10664],[-10664]],[[0,0],[0]],[[-116145840,-124],[-124]],[[0]],[[-20153100]],[[0]],[[-2406685]],[[0]],[[-180017]],[[0]],[[-6851]],[[0]],[[-62]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
