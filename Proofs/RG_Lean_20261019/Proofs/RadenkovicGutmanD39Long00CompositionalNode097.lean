/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode051
import Proofs.RadenkovicGutmanD39Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e097 : NestedArithmetic.Expr 3 := .times e051 e057
noncomputable def p097 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-4563],[0,-4563]],[[0,0,0],[0,0,0],[0,0]],[[0,41067,-68445],[41067,-205335,-20007],[-68445,-20007]],[[0,0,0],[0,0,0],[0,0]],[[616005,-1357317,-526851],[-1357317,-1513512,-25350],[-526851,-25350]],[[0,0,0],[0,0,0],[0,0]],[[-3522285,-16532100,-1614834],[-16532100,-4437927,-11895],[-1614834,-11895]],[[0,0,0],[0,0,0],[0,0]],[[-103928994,-77643189,-2585349],[-77643189,-6837636,-2067],[-2585349,-2067]],[[0,0,0],[0,0,0],[0,0]],[[-723036483,-204257976,-2377050],[-204257976,-6095856,-78],[-2377050,-78]],[[0,0,0],[0,0],[0]],[[-2738595951,-341610165,-1295307],[-341610165,-3245346],[-1295307]],[[0,0,0],[0,0],[0]],[[-6739539924,-385537854,-414258],[-385537854,-1021527],[-414258]],[[0,0,0],[0,0],[0]],[[-11646735360,-302458221,-72735],[-302458221,-178152],[-72735]],[[0,0,0],[0,0],[0]],[[-14740921143,-166845003,-5733],[-166845003,-14235],[-5733]],[[0,0,0],[0,0],[0]],[[-14001986154,-64504674,-78],[-64504674,-234],[-78]],[[0,0],[0]],[[-10118552652,-17137146],[-17137146]],[[0,0],[0]],[[-5595375708,-2993562],[-2993562]],[[0,0],[0]],[[-2365276329,-313872],[-313872]],[[0,0],[0]],[[-758121507,-15912],[-15912]],[[0,0],[0]],[[-181134720,-156],[-156]],[[0]],[[-31306860]],[[0]],[[-3715725]],[[0]],[[-274833]],[[0]],[[-10179]],[[0]],[[-78]]]
theorem step097 : p097=NestedArithmetic.mul p051 p057 := by decide +kernel
#print axioms step097
theorem h097 : NestedArithmetic.compile e097=p097 := StagedExprCompile.compile_times e097 e051 e057 p051 p057 p097 rfl h051 h057 step097
#print axioms h097
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
