/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode051
import Proofs.RadenkovicGutmanD27Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-2187],[0,-2187]],[[0,0,0],[0,0,0],[0,0]],[[0,19683,-32805],[19683,-98415,-9639],[-32805,-9639]],[[0,0,0],[0,0,0],[0,0]],[[295245,-650997,-252963],[-650997,-727056,-12366],[-252963,-12366]],[[0,0,0],[0,0,0],[0,0]],[[-1694925,-7940268,-777114],[-7940268,-2138319,-5967],[-777114,-5967]],[[0,0,0],[0,0,0],[0,0]],[[-49975866,-37347885,-1247805],[-37347885,-3307500,-1107],[-1247805,-1107]],[[0,0,0],[0,0,0],[0,0]],[[-347974299,-98416512,-1151874],[-98416512,-2964384,-54],[-1151874,-54]],[[0,0,0],[0,0],[0]],[[-1319340879,-164909277,-631395],[-164909277,-1590354],[-631395]],[[0,0,0],[0,0],[0]],[[-3250486044,-186530310,-203850],[-186530310,-506655],[-203850]],[[0,0,0],[0,0],[0]],[[-5624191152,-146732229,-36423],[-146732229,-90288],[-36423]],[[0,0,0],[0,0],[0]],[[-7128196911,-81220779,-2997],[-81220779,-7587],[-2997]],[[0,0,0],[0,0],[0]],[[-6781500738,-31545450,-54],[-31545450,-162],[-54]],[[0,0],[0]],[[-4909617036,-8435610],[-8435610]],[[0,0],[0]],[[-2720868732,-1488618],[-1488618]],[[0,0],[0]],[[-1153274193,-158976],[-158976]],[[0,0],[0]],[[-370930995,-8424],[-8424]],[[0,0],[0]],[[-89038440,-108],[-108]],[[0]],[[-15492060]],[[0]],[[-1858005]],[[0]],[[-140049]],[[0]],[[-5427]],[[0]],[[-54]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
