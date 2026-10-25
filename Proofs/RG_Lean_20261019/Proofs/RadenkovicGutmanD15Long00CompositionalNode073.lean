/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode071
import Proofs.RadenkovicGutmanD15Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-12150,0],[-12150,-3105,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-210195,-234495,0],[-234495,-35280,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-4334715,-1902690,0],[-1902690,-163965,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-39478590,-8664615,0],[-8664615,-404460,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-211614885,-24846750,0],[-24846750,-579120,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-750172395,-47659845,0],[-47659845,-499170,0],[0,0]],[[0,0,0],[0,0],[0]],[[-1873138380,-63376530,0],[-63376530,-260445],[0]],[[0,0,0],[0,0],[0]],[[-3424800120,-59684220,0],[-59684220,-80160],[0]],[[0,0,0],[0,0],[0]],[[-4703194155,-40234830,0],[-40234830,-13365],[0]],[[0,0,0],[0,0],[0]],[[-4933144740,-19435695,0],[-19435695,-930],[0]],[[0,0,0],[0,0],[0]],[[-3993636630,-6660330,0],[-6660330,0],[0]],[[0,0],[0]],[[-2508482100,-1578525],[-1578525]],[[0,0],[0]],[[-1222994115,-245790],[-245790]],[[0,0],[0]],[[-460601355,-22605],[-22605]],[[0,0],[0]],[[-132520020,-930],[-930]],[[0,0],[0]],[[-28554300,0],[0]],[[0]],[[-4456125]],[[0]],[[-475275]],[[0]],[[-30975]],[[0]],[[-930]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
