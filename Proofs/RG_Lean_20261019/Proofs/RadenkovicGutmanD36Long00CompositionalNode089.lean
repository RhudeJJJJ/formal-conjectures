/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode033
import Proofs.RadenkovicGutmanD36Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e089 : NestedArithmetic.Expr 3 := .times e033 e061
noncomputable def p089 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,3888],[0,3888,-2448]],[[0,0,0],[0,0,0],[0,0]],[[0,-34992,34992],[-34992,128304,-27216],[34992,-27216]],[[0,0,0],[0,0,0],[0,0]],[[-326592,384912,46656],[384912,85536,-96768],[46656,-96768]],[[0,0,0],[0,0,0],[0,0]],[[112752,1842912,-381024],[1842912,-1867536,-98640],[-381024,-98640]],[[0,0,0],[0,0,0],[0,0]],[[12328848,-4060368,-1398384],[-4060368,-6187104,-37872],[-1398384,-37872]],[[0,0,0],[0,0,0],[0,0]],[[35678448,-41671584,-2113344],[-41671584,-9028800,-4896],[-2113344,-4896]],[[0,0,0],[0,0],[0]],[[-68965920,-121524624,-1755504],[-121524624,-7346016],[-1755504]],[[0,0,0],[0,0],[0]],[[-679743072,-200693376,-857376],[-200693376,-3534480],[-857376]],[[0,0,0],[0,0],[0]],[[-2101636512,-215839728,-244944],[-215839728,-997920],[-244944]],[[0,0,0],[0,0],[0]],[[-3949736976,-159416784,-37872],[-159416784,-152784],[-37872]],[[0,0,0],[0,0],[0]],[[-5153890176,-82478304,-2448],[-82478304,-9792],[-2448]],[[0,0],[0]],[[-4925382912,-29868480],[-29868480]],[[0,0],[0]],[[-3536164224,-7417728],[-7417728]],[[0,0],[0]],[[-1928746800,-1203552],[-1203552]],[[0,0],[0]],[[-800422560,-114912],[-114912]],[[0,0],[0]],[[-250922016,-4896],[-4896]],[[0]],[[-58403808]],[[0]],[[-9778608]],[[0]],[[-1112832]],[[0]],[[-77040]],[[0]],[[-2448]]]
theorem step089 : p089=NestedArithmetic.mul p033 p061 := by decide +kernel
#print axioms step089
theorem h089 : NestedArithmetic.compile e089=p089 := StagedExprCompile.compile_times e089 e033 e061 p033 p061 p089 rfl h033 h061 step089
#print axioms h089
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
