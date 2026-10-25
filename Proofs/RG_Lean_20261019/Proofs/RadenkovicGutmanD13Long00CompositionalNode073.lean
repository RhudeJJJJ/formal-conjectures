/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode071
import Proofs.RadenkovicGutmanD13Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-9126,0],[-9126,-2457,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-159003,-177255,0],[-177255,-27612,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3285711,-1442142,0],[-1442142,-127101,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-29952234,-6573047,0],[-6573047,-311064,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-160593069,-18848258,0],[-18848258,-442728,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-569234575,-36137829,0],[-36137829,-379938,0],[0,0]],[[0,0,0],[0,0],[0]],[[-1420891056,-48026342,0],[-48026342,-197613],[0]],[[0,0,0],[0,0],[0]],[[-2596822592,-45200012,0],[-45200012,-60684],[0]],[[0,0,0],[0,0],[0]],[[-3564489123,-30452214,0],[-30452214,-10101],[0]],[[0,0,0],[0,0],[0]],[[-3736986968,-14701895,0],[-14701895,-702],[0]],[[0,0,0],[0,0],[0]],[[-3023875790,-5035550,0],[-5035550,0],[0]],[[0,0],[0]],[[-1898510172,-1192893],[-1192893]],[[0,0],[0]],[[-925217579,-185666],[-185666]],[[0,0],[0]],[[-348316631,-17069],[-17069]],[[0,0],[0]],[[-100177896,-702],[-702]],[[0,0],[0]],[[-21578180,0],[0]],[[0]],[[-3366389]],[[0]],[[-358943]],[[0]],[[-23387]],[[0]],[[-702]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
