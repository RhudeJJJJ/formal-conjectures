/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD11Long00CompositionalNode079
import Proofs.RadenkovicGutmanD11Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-6534,0],[-6534,-1089,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-107811,-94743,0],[-94743,-9438,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1760913,-583704,0],[-583704,-32065,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-12793572,-2022515,0],[-2022515,-55418,0],[0,0]],[[0,0,0],[0,0],[0]],[[-54963645,-4408272,0],[-4408272,-53724],[0]],[[0,0,0],[0,0],[0]],[[-156710609,-6415057,0],[-6415057,-30250],[0]],[[0,0,0],[0,0],[0]],[[-315540654,-6451236,0],[-6451236,-9801],[0]],[[0,0,0],[0,0],[0]],[[-465985036,-4567508,0],[-4567508,-1694],[0]],[[0,0,0],[0,0],[0]],[[-517025619,-2290530,0],[-2290530,-121],[0]],[[0,0],[0]],[[-437552214,-808159],[-808159]],[[0,0],[0]],[[-284806170,-196020],[-196020]],[[0,0],[0]],[[-142945528,-31097],[-31097]],[[0,0],[0]],[[-55140547,-2904],[-2904]],[[0,0],[0]],[[-16184597,-121],[-121]],[[0]],[[-3546510]],[[0]],[[-561440]],[[0]],[[-60621]],[[0]],[[-3993]],[[0]],[[-121]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree11Long00Compositional
