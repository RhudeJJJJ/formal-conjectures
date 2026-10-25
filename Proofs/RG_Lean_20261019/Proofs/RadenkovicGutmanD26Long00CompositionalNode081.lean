/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD26Long00CompositionalNode079
import Proofs.RadenkovicGutmanD26Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-36504,0],[-36504,-6084,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-602316,-529308,0],[-529308,-52728,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-9837828,-3261024,0],[-3261024,-179140,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-71474832,-11299340,0],[-11299340,-309608,0],[0,0]],[[0,0,0],[0,0],[0]],[[-307069620,-24628032,0],[-24628032,-300144],[0]],[[0,0,0],[0,0],[0]],[[-875507204,-35839492,0],[-35839492,-169000],[0]],[[0,0,0],[0,0],[0]],[[-1762855224,-36041616,0],[-36041616,-54756],[0]],[[0,0,0],[0,0],[0]],[[-2603354416,-25517648,0],[-25517648,-9464],[0]],[[0,0,0],[0,0],[0]],[[-2888506764,-12796680,0],[-12796680,-676],[0]],[[0,0],[0]],[[-2444506584,-4515004],[-4515004]],[[0,0],[0]],[[-1591148520,-1095120],[-1095120]],[[0,0],[0]],[[-798604768,-173732],[-173732]],[[0,0],[0]],[[-308057932,-16224],[-16224]],[[0,0],[0]],[[-90419732,-676],[-676]],[[0]],[[-19813560]],[[0]],[[-3136640]],[[0]],[[-338676]],[[0]],[[-22308]],[[0]],[[-676]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree26Long00Compositional
