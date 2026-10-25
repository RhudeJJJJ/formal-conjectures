/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD39Long00CompositionalNode073
import Proofs.RadenkovicGutmanD39Long00CompositionalNode084
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e085 : NestedArithmetic.Expr 3 := .plus e073 e084
noncomputable def p085 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,-2808,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-25272,-353808,0],[-353808,-79794,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-6092658,-5056506,0],[-5056506,-563316,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-95277546,-30810780,0],[-30810780,-1775826,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-680325984,-105869790,0],[-105869790,-2960724,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-2893491042,-229302060,0],[-229302060,-2813928,0],[0,0]],[[0,0,0],[0,0],[0]],[[-8193574974,-332084766,0],[-332084766,-1565772],[0]],[[0,0,0],[0,0],[0]],[[-16415083308,-332711496,0],[-332711496,-503490],[0]],[[0,0,0],[0,0],[0]],[[-24147213792,-234865020,0],[-234865020,-86580],[0]],[[0,0,0],[0,0],[0]],[[-26708621550,-117499512,0],[-117499512,-6162],[0]],[[0,0,0],[0,0],[0]],[[-22545305484,-41375334,0],[-41375334,0],[0]],[[0,0],[0]],[[-14643468060,-10019100],[-10019100]],[[0,0],[0]],[[-7336237896,-1587222],[-1587222]],[[0,0],[0]],[[-2825482686,-148044],[-148044]],[[0,0],[0]],[[-828191910,-6162],[-6162]],[[0,0],[0]],[[-181263420,0],[0]],[[0]],[[-28665000]],[[0]],[[-3092154]],[[0]],[[-203502]],[[0]],[[-6162]],[[0]],[[0]]]
theorem step085 : p085=NestedHorner.add p073 p084 := by decide +kernel
#print axioms step085
theorem h085 : NestedArithmetic.compile e085=p085 := StagedExprCompile.compile_plus e085 e073 e084 p073 p084 p085 rfl h073 h084 step085
#print axioms h085
end Gebendorfer.RadenkovicGutman.FixedDegree39Long00Compositional
