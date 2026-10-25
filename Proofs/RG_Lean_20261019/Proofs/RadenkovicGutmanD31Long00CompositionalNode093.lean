/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode033
import Proofs.RadenkovicGutmanD31Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,961]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,23064],[0,23064,62]],[[0,0,0],[0,0,0],[0,0]],[[-77841,-51894,129735],[-51894,501642,72230],[129735,72230]],[[0,0,0],[0,0,0],[0,0]],[[-2132676,1971972,783432],[1971972,2983812,76012],[783432,76012]],[[0,0,0],[0,0,0],[0,0]],[[-9142551,19325772,1964160],[19325772,7347310,31558],[1964160,31558]],[[0,0,0],[0,0,0],[0,0]],[[22036722,77213002,2668418],[77213002,9793396,4836],[2668418,4836]],[[0,0,0],[0,0,0],[0,0]],[[315078389,177635580,2148238],[177635580,7739584,124],[2148238,124]],[[0,0,0],[0,0],[0]],[[1305331508,265356652,1052450],[265356652,3729300],[1052450]],[[0,0,0],[0,0],[0]],[[3217637002,272282672,309256],[272282672,1081342],[309256]],[[0,0,0],[0,0],[0]],[[5446439600,197200858,50902],[197200858,176700],[50902]],[[0,0,0],[0,0],[0]],[[6718557026,101775046,3875],[101775046,13578],[3875]],[[0,0,0],[0,0],[0]],[[6225144596,37255986,62],[37255986,248],[62]],[[0,0],[0]],[[4400980224,9479800],[9479800]],[[0,0],[0]],[[2389505048,1606420],[1606420]],[[0,0],[0]],[[995673841,166532],[166532]],[[0,0],[0]],[[315928812,8742],[8742]],[[0,0],[0]],[[75101778,124],[124]],[[0]],[[13001896]],[[0]],[[1562369]],[[0]],[[119536]],[[0]],[[4867]],[[0]],[[62]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
