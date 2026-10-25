/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode217
import Proofs.RadenkovicGutmanD8Long00CompositionalNode219
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e220 : NestedArithmetic.Expr 3 := .times e217 e219
noncomputable def p220 : NestedHorner.Poly 3 := [[[-128],[0],[0]],[[0,0],[0,0],[0]],[[-3968,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-56448,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-488448,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-2873088,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-12161792,-192,0],[-192,0],[0]],[[0,0,0],[0,0],[0]],[[-38260352,-4288,0],[-4288,0],[0]],[[0,0,0],[0,0],[0]],[[-91096192,-42560,0],[-42560,0],[0]],[[0,0,0],[0,0],[0]],[[-165614592,-247424,0],[-247424,0],[0]],[[0,0,0],[0,0],[0]],[[-230269312,-934976,0],[-934976,0],[0]],[[0,0,0],[0,0],[0]],[[-243609984,-2410176,-64],[-2410176,-128],[-64]],[[0,0,0],[0,0],[0]],[[-193671424,-4328704,-896],[-4328704,-1792],[-896]],[[0,0,0],[0,0],[0]],[[-113190144,-5435968,-5184],[-5435968,-10368],[-5184]],[[0,0,0],[0,0],[0]],[[-46900224,-4718272,-16000],[-4718272,-32000],[-16000]],[[0,0,0],[0,0],[0]],[[-12956544,-2748800,-28416],[-2748800,-56832],[-28416]],[[0,0,0],[0,0],[0]],[[-2125440,-1015488,-29312],[-1015488,-58624],[-29312]],[[0,0,0],[0,0],[0]],[[-155520,-212544,-16960],[-212544,-33920],[-16960]],[[0,0,0],[0,0],[0]],[[0,-19008,-4992],[-19008,-9984],[-4992]],[[0,0,0],[0,0],[0]],[[0,0,-576],[0,-1152],[-576]]]
theorem step220 : p220=NestedArithmetic.mul p217 p219 := by decide +kernel
#print axioms step220
theorem h220 : NestedArithmetic.compile e220=p220 := StagedExprCompile.compile_times e220 e217 e219 p217 p219 p220 rfl h217 h219 step220
#print axioms h220
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
