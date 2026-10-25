/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD22Long00CompositionalNode071
import Proofs.RadenkovicGutmanD22Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-26136,0],[-26136,-5940,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-445500,-497772,0],[-497772,-69300,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-9147600,-4015836,0],[-4015836,-329340,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-83149308,-18253796,0],[-18253796,-826980,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-445453140,-52348868,0],[-52348868,-1199880,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1579517632,-100507836,0],[-100507836,-1044120,0],[0,0]],[[0,0,0],[0,0],[0]],[[-3946666284,-133821380,0],[-133821380,-548460],[0]],[[0,0,0],[0,0],[0]],[[-7222500824,-126192704,0],[-126192704,-169620],[0]],[[0,0,0],[0,0],[0]],[[-9928338156,-85179072,0],[-85179072,-28380],[0]],[[0,0,0],[0,0],[0]],[[-10424294012,-41195132,0],[-41195132,-1980],[0]],[[0,0,0],[0,0],[0]],[[-8447352848,-14132228,0],[-14132228,0],[0]],[[0,0],[0]],[[-5310960072,-3352668],[-3352668]],[[0,0],[0]],[[-2591626268,-522500],[-522500]],[[0,0],[0]],[[-976862744,-48092],[-48092]],[[0,0],[0]],[[-281270748,-1980],[-1980]],[[0,0],[0]],[[-60649160,0],[0]],[[0]],[[-9471044]],[[0]],[[-1010768]],[[0]],[[-65912]],[[0]],[[-1980]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree22Long00Compositional
