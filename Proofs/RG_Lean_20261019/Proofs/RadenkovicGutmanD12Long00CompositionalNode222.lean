/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD12Long00CompositionalNode221
import Proofs.RadenkovicGutmanD12Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e222 : NestedArithmetic.Expr 3 := .times e221 e003
noncomputable def p222 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[288,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[8928,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[127008,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1099008,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[6464448,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[27364032,432,0],[432,0],[0]],[[0,0,0],[0,0],[0]],[[86085792,9648,0],[9648,0],[0]],[[0,0,0],[0,0],[0]],[[204966432,95760,0],[95760,0],[0]],[[0,0,0],[0,0],[0]],[[372632832,556704,0],[556704,0],[0]],[[0,0,0],[0,0],[0]],[[518105952,2103696,0],[2103696,0],[0]],[[0,0,0],[0,0],[0]],[[548122464,5422896,144],[5422896,288],[144]],[[0,0,0],[0,0],[0]],[[435760704,9739584,2016],[9739584,4032],[2016]],[[0,0,0],[0,0],[0]],[[254677824,12230928,11664],[12230928,23328],[11664]],[[0,0,0],[0,0],[0]],[[105525504,10616112,36000],[10616112,72000],[36000]],[[0,0,0],[0,0],[0]],[[29152224,6184800,63936],[6184800,127872],[63936]],[[0,0,0],[0,0],[0]],[[4782240,2284848,65952],[2284848,131904],[65952]],[[0,0,0],[0,0],[0]],[[349920,478224,38160],[478224,76320],[38160]],[[0,0,0],[0,0],[0]],[[0,42768,11232],[42768,22464],[11232]],[[0,0,0],[0,0],[0]],[[0,0,1296],[0,2592],[1296]]]
theorem step222 : p222=NestedArithmetic.mul p221 p003 := by decide +kernel
#print axioms step222
theorem h222 : NestedArithmetic.compile e222=p222 := StagedExprCompile.compile_times e222 e221 e003 p221 p003 p222 rfl h221 h003 step222
#print axioms h222
end Gebendorfer.RadenkovicGutman.FixedDegree12Long00Compositional
