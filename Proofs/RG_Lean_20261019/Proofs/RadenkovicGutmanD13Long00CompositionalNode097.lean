/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode051
import Proofs.RadenkovicGutmanD13Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-507],[0,-507]],[[0,0,0],[0,0,0],[0,0]],[[0,4563,-7605],[4563,-22815,-2275],[-7605,-2275]],[[0,0,0],[0,0,0],[0,0]],[[68445,-151281,-59007],[-151281,-169884,-3042],[-59007,-3042]],[[0,0,0],[0,0,0],[0,0]],[[-398385,-1854216,-182702],[-1854216,-504855,-1599],[-182702,-1599]],[[0,0,0],[0,0,0],[0,0]],[[-11718486,-8767109,-296309],[-8767109,-791336,-351],[-296309,-351]],[[0,0,0],[0,0,0],[0,0]],[[-81829371,-23235420,-277238],[-23235420,-721864,-26],[-277238,-26]],[[0,0,0],[0,0],[0]],[[-311339899,-39186589,-154947],[-39186589,-396994],[-154947]],[[0,0,0],[0,0],[0]],[[-770006952,-44658874,-51558],[-44658874,-131287],[-51558]],[[0,0,0],[0,0],[0]],[[-1337925784,-35449869,-9711],[-35449869,-24908],[-9711]],[[0,0,0],[0,0],[0]],[[-1703624975,-19846151,-897],[-19846151,-2379],[-897]],[[0,0,0],[0,0],[0]],[[-1629311710,-7823374,-26],[-7823374,-78],[-26]],[[0,0],[0]],[[-1186768284,-2135666],[-2135666]],[[0,0],[0]],[[-662457692,-388778],[-388778]],[[0,0],[0]],[[-283277345,-43784],[-43784]],[[0,0],[0]],[[-92133847,-2600],[-2600]],[[0,0],[0]],[[-22444500,-52],[-52]],[[0]],[[-3986580]],[[0]],[[-493285]],[[0]],[[-39221]],[[0]],[[-1703]],[[0]],[[-26]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
