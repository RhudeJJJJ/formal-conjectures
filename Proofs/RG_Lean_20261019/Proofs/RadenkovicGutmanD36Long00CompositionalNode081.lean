/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode079
import Proofs.RadenkovicGutmanD36Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-69984,0],[-69984,-11664,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1154736,-1014768,0],[-1014768,-101088,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-18860688,-6251904,0],[-6251904,-343440,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-137028672,-21662640,0],[-21662640,-593568,0],[0,0]],[[0,0,0],[0,0],[0]],[[-588701520,-47215872,0],[-47215872,-575424],[0]],[[0,0,0],[0,0],[0]],[[-1678487184,-68710032,0],[-68710032,-324000],[0]],[[0,0,0],[0,0],[0]],[[-3379675104,-69097536,0],[-69097536,-104976],[0]],[[0,0,0],[0,0],[0]],[[-4991046336,-48921408,0],[-48921408,-18144],[0]],[[0,0,0],[0,0],[0]],[[-5537728944,-24533280,0],[-24533280,-1296],[0]],[[0,0],[0]],[[-4686509664,-8655984],[-8655984]],[[0,0],[0]],[[-3050485920,-2099520],[-2099520]],[[0,0],[0]],[[-1531052928,-333072],[-333072]],[[0,0],[0]],[[-590596272,-31104],[-31104]],[[0,0],[0]],[[-173349072,-1296],[-1296]],[[0]],[[-37985760]],[[0]],[[-6013440]],[[0]],[[-649296]],[[0]],[[-42768]],[[0]],[[-1296]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
