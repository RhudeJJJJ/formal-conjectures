/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode035
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e114 : NestedArithmetic.Expr 3 := .pow e035 2
noncomputable def p114 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,2025],[0,4050],[2025]],[[0,0,0],[0,0],[0]],[[0,72900,17550],[72900,35100],[17550]],[[0,0,0],[0,0],[0]],[[656100,826200,59625],[826200,119250],[59625]],[[0,0,0],[0,0],[0]],[[9185400,4009500,103050],[4009500,206100],[103050]],[[0,0,0],[0,0],[0]],[[57518100,11043000,99900],[11043000,199800],[99900]],[[0,0,0],[0,0],[0]],[[214374600,19305900,56250],[19305900,112500],[56250]],[[0,0,0],[0,0],[0]],[[533676600,22662000,18225],[22662000,36450],[18225]],[[0,0,0],[0,0],[0]],[[943147800,18383400,3150],[18383400,6300],[3150]],[[0,0,0],[0,0],[0]],[[1226421900,10422000,225],[10422000,450],[225]],[[0,0],[0]],[[1199053800,4113900],[4113900]],[[0,0],[0]],[[892189800,1107000],[1107000]],[[0,0],[0]],[[507709800,193500],[193500]],[[0,0],[0]],[[220574700,19800],[19800]],[[0,0],[0]],[[72509400,900],[900]],[[0]],[[17710200]],[[0]],[[3112200]],[[0]],[[371700]],[[0]],[[27000]],[[0]],[[900]]]
theorem step114 : p114=NestedArithmetic.power p035 2 := by decide +kernel
#print axioms step114
theorem h114 : NestedArithmetic.compile e114=p114 := StagedExprCompile.compile_pow 2 e114 e035 p035 p114 rfl h035 step114
#print axioms h114
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
