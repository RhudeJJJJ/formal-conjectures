/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode093
import Proofs.RadenkovicGutmanD24Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,576]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-5184],[0,-10368,16992],[-5184,16992,48]],[[0,0,0],[0,0,0],[0,0]],[[-46656,-173664,61344],[-173664,324864,57216],[61344,57216]],[[0,0,0],[0,0,0],[0,0]],[[-2165616,409536,517392],[409536,2284992,62976],[517392,62976]],[[0,0,0],[0,0,0],[0,0]],[[-11964672,11963808,1469376],[11963808,6099840,26784],[1469376,26784]],[[0,0,0],[0,0,0],[0,0]],[[9688464,59275200,2153568],[59275200,8598144,4128],[2153568,4128]],[[0,0,0],[0,0,0],[0,0]],[[316414656,152345664,1828224],[152345664,7089408,96],[1828224,96]],[[0,0,0],[0,0],[0]],[[1465050768,244698048,930624],[244698048,3527808],[930624]],[[0,0,0],[0,0],[0]],[[3824834304,264474336,280896],[264474336,1046400],[280896]],[[0,0,0],[0,0],[0]],[[6714481824,199041120,46944],[199041120,172800],[46944]],[[0,0,0],[0,0],[0]],[[8484833664,105673056,3552],[105673056,13056],[3552]],[[0,0,0],[0,0],[0]],[[7985078784,39466272,48],[39466272,192],[48]],[[0,0],[0]],[[5697388032,10167840],[10167840]],[[0,0],[0]],[[3106403712,1729632],[1729632]],[[0,0],[0]],[[1294430400,177600],[177600]],[[0,0],[0]],[[409172496,8928],[8928]],[[0,0],[0]],[[96512256,96],[96]],[[0]],[[16495008]],[[0]],[[1941312]],[[0]],[[143184]],[[0]],[[5376]],[[0]],[[48]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
