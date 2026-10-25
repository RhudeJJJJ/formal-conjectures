/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD27Long00CompositionalNode096
import Proofs.RadenkovicGutmanD27Long00CompositionalNode098
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .plus e096 e098
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,4374],[0,4374,-1350]],[[0,0,0],[0,0,0],[0,0]],[[0,0,52488],[0,179091,-5184],[52488,-5184]],[[0,0,0],[0,0,0],[0,0]],[[185895,1455813,281394],[1455813,857628,-40770],[281394,-40770]],[[0,0,0],[0,0,0],[0,0]],[[12790305,12731256,574452],[12731256,1384911,-48330],[574452,-48330]],[[0,0,0],[0,0,0],[0,0]],[[138422520,48526371,487458],[48526371,365040,-19764],[487458,-19764]],[[0,0,0],[0,0,0],[0,0]],[[724253319,105313986,-4482],[105313986,-1565136,-2646],[-4482,-2646]],[[0,0,0],[0,0],[0]],[[2313723555,142225605,-332154],[142225605,-2209842],[-332154]],[[0,0,0],[0,0],[0]],[[4985023068,121278060,-267624],[121278060,-1361745],[-267624]],[[0,0,0],[0,0],[0]],[[7624985220,60464178,-98442],[60464178,-446148],[-98442]],[[0,0,0],[0,0],[0]],[[8505532845,10044432,-17874],[10044432,-75681],[-17874]],[[0,0,0],[0,0],[0]],[[6990629724,-7921773,-1296],[-7921773,-5238],[-1296]],[[0,0],[0]],[[4207523346,-6548580],[-6548580]],[[0,0],[0]],[[1795935996,-2361501],[-2361501]],[[0,0],[0]],[[490678857,-481842],[-481842]],[[0,0],[0]],[[48911715,-53973],[-53973]],[[0,0],[0]],[[-22801500,-2592],[-2592]],[[0]],[[-12454560]],[[0]],[[-3067821]],[[0]],[[-442449]],[[0]],[[-36099]],[[0]],[[-1296]]]
theorem step099 : p099=NestedHorner.add p096 p098 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_plus e099 e096 e098 p096 p098 p099 rfl h096 h098 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree27Long00Compositional
