/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD43Long00CompositionalNode093
import Proofs.RadenkovicGutmanD43Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1849]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-16641],[0,-33282,54954],[-16641,54954,86]],[[0,0,0],[0,0,0],[0,0]],[[-149769,-553797,200595],[-553797,1057542,184212],[200595,184212]],[[0,0,0],[0,0,0],[0,0]],[[-6880086,1461699,1681085],[1461699,7415866,201068],[1681085,201068]],[[0,0,0],[0,0,0],[0,0]],[[-36679473,39530889,4758466],[39530889,19747578,83936],[4758466,83936]],[[0,0,0],[0,0,0],[0,0]],[[45981276,194332824,6950004],[194332824,27748244,12298],[6950004,12298]],[[0,0,0],[0,0,0],[0,0]],[[1085172725,497527157,5873628],[497527157,22777100,172],[5873628,172]],[[0,0,0],[0,0],[0]],[[4908791420,796697163,2970483],[796697163,11256970],[2970483]],[[0,0,0],[0,0],[0]],[[12697389590,858490184,887262],[858490184,3301282],[887262]],[[0,0,0],[0,0],[0]],[[22167611034,643892965,145383],[643892965,533458],[145383]],[[0,0,0],[0,0],[0]],[[27897546192,340416251,10449],[340416251,38098],[10449]],[[0,0,0],[0,0],[0]],[[26161164912,126431438,86],[126431438,344],[86]],[[0,0],[0]],[[18601915154,32314715],[32314715]],[[0,0],[0]],[[10105517806,5428191],[5428191]],[[0,0],[0]],[[4193546749,544509],[544509]],[[0,0],[0]],[[1318937108,25800],[25800]],[[0,0],[0]],[[309070842,172],[172]],[[0]],[[52339686]],[[0]],[[6072159]],[[0]],[[436278]],[[0]],[[15351]],[[0]],[[86]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree43Long00Compositional
