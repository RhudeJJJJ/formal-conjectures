/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode076
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e077 : NestedArithmetic.Expr 3 := .scaled (-1) e076
noncomputable def p077 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,576],[0,1152],[576]],[[0,0,0],[0,0],[0]],[[0,19008,4992],[19008,9984],[4992]],[[0,0,0],[0,0],[0]],[[155520,212544,16960],[212544,33920],[16960]],[[0,0,0],[0,0],[0]],[[2125440,1015488,29312],[1015488,58624],[29312]],[[0,0,0],[0,0],[0]],[[12956544,2748800,28416],[2748800,56832],[28416]],[[0,0,0],[0,0],[0]],[[46900224,4718272,16000],[4718272,32000],[16000]],[[0,0,0],[0,0],[0]],[[113190144,5435968,5184],[5435968,10368],[5184]],[[0,0,0],[0,0],[0]],[[193671424,4328704,896],[4328704,1792],[896]],[[0,0,0],[0,0],[0]],[[243609984,2410176,64],[2410176,128],[64]],[[0,0],[0]],[[230269312,934976],[934976]],[[0,0],[0]],[[165614592,247424],[247424]],[[0,0],[0]],[[91096192,42560],[42560]],[[0,0],[0]],[[38260352,4288],[4288]],[[0,0],[0]],[[12161792,192],[192]],[[0]],[[2873088]],[[0]],[[488448]],[[0]],[[56448]],[[0]],[[3968]],[[0]],[[128]]]
theorem step077 : p077=NestedHorner.scale (-1) p076 := by decide +kernel
#print axioms step077
theorem h077 : NestedArithmetic.compile e077=p077 := StagedExprCompile.compile_scaled (-1) e077 e076 p076 p077 rfl h076 step077
#print axioms h077
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
