/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode043
import Proofs.RadenkovicGutmanD31Long00CompositionalNode057
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e100 : NestedArithmetic.Expr 3 := .times e043 e057
noncomputable def p100 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-8649],[0,-17298,5394],[-8649,5394]],[[0,0,0],[0,0,0],[0,0]],[[0,-340659,-26412],[-340659,28086,23374],[-26412,23374]],[[0,0,0],[0,0,0],[0,0]],[[-3163860,-2744523,85157],[-2744523,709714,28768],[85157,28768]],[[0,0,0],[0,0,0],[0,0]],[[-38066760,-8224083,498418],[-8224083,2397478,12586],[498418,12586]],[[0,0,0],[0,0,0],[0,0]],[[-202525542,-8814788,934402],[-8814788,3767492,1798],[934402,1798]],[[0,0,0],[0,0],[0]],[[-627708150,10291721,903278],[10291721,3295300],[903278]],[[0,0,0],[0,0],[0]],[[-1247498094,46634137,495721],[46634137,1689066],[495721]],[[0,0,0],[0,0],[0]],[[-1624242520,72141712,155558],[72141712,503502],[155558]],[[0,0,0],[0,0],[0]],[[-1292681214,66177715,26009],[66177715,80786],[26009]],[[0,0,0],[0,0],[0]],[[-362122532,39900937,1798],[39900937,5394],[1798]],[[0,0],[0]],[[510988376,16250882],[16250882]],[[0,0],[0]],[[824312630,4436875],[4436875]],[[0,0],[0]],[[646438102,779061],[779061]],[[0,0],[0]],[[335338098,79577],[79577]],[[0,0],[0]],[[122888154,3596],[3596]],[[0]],[[32172420]],[[0]],[[5911390]],[[0]],[[725896]],[[0]],[[53568]],[[0]],[[1798]]]
theorem step100 : p100=NestedArithmetic.mul p043 p057 := by decide +kernel
#print axioms step100
theorem h100 : NestedArithmetic.compile e100=p100 := StagedExprCompile.compile_times e100 e043 e057 p043 p057 p100 rfl h043 h057 step100
#print axioms h100
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
