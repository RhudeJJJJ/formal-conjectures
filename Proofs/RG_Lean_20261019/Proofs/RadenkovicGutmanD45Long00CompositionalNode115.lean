/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD45Long00CompositionalNode113
import Proofs.RadenkovicGutmanD45Long00CompositionalNode114
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e115 : NestedArithmetic.Expr 3 := .plus e113 e114
noncomputable def p115 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,2025]],[[0,0],[0,0,0],[0,0]],[[0,0,18225],[0,0,36450],[18225,36450]],[[0,0,0],[0,0,0],[0,0]],[[164025,328050,321975],[328050,656100,97200],[321975,97200]],[[0,0,0],[0,0,0],[0,0]],[[5795550,6670350,1411425],[6670350,3499200,89100],[1411425,89100]],[[0,0,0],[0,0,0],[0,0]],[[76599675,41662350,2895750],[41662350,7873200,32400],[2895750,32400]],[[0,0,0],[0,0,0],[0,0]],[[500956650,134330400,3329100],[134330400,9720000,4050],[3329100,4050]],[[0,0,0],[0,0],[0]],[[1964535525,266210550,2300400],[266210550,7176600],[2300400]],[[0,0,0],[0,0],[0]],[[5136736500,351843750,974025],[351843750,3240000],[974025]],[[0,0,0],[0,0],[0]],[[9530747550,323586900,247050],[323586900,874800],[247050]],[[0,0,0],[0,0],[0]],[[13042170450,211474800,34425],[211474800,129600],[34425]],[[0,0,0],[0,0],[0]],[[13489156800,98799750,2025],[98799750,8100],[2025]],[[0,0],[0]],[[10704798000,32744250],[32744250]],[[0,0],[0]],[[6571044000,7512750],[7512750]],[[0,0],[0]],[[3126563550,1134000],[1134000]],[[0,0],[0]],[[1148784525,101250],[101250]],[[0,0],[0]],[[322533900,4050],[4050]],[[0]],[[67857750]],[[0]],[[10347750]],[[0]],[[1079325]],[[0]],[[68850]],[[0]],[[2025]]]
theorem step115 : p115=NestedHorner.add p113 p114 := by decide +kernel
#print axioms step115
theorem h115 : NestedArithmetic.compile e115=p115 := StagedExprCompile.compile_plus e115 e113 e114 p113 p114 p115 rfl h113 h114 step115
#print axioms h115
end Gebendorfer.RadenkovicGutman.FixedDegree45Long00Compositional
