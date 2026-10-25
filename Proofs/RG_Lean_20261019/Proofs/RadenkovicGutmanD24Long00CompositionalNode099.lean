/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode096
import Proofs.RadenkovicGutmanD24Long00CompositionalNode098
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .plus e096 e098
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,3456],[0,3456,-1056]],[[0,0,0],[0,0,0],[0,0]],[[0,0,41472],[0,141696,-3888],[41472,-3888]],[[0,0,0],[0,0,0],[0,0]],[[147744,1152144,223344],[1152144,683280,-31632],[223344,-31632]],[[0,0,0],[0,0,0],[0,0]],[[10138608,10099728,459504],[10099728,1121952,-37632],[459504,-37632]],[[0,0,0],[0,0,0],[0,0]],[[109826928,38604384,398304],[38604384,349392,-15408],[398304,-15408]],[[0,0,0],[0,0,0],[0,0]],[[575347392,84084816,13296],[84084816,-1162272,-2064],[13296,-2064]],[[0,0,0],[0,0],[0]],[[1840645104,114156480,-249600],[114156480,-1691712],[-249600]],[[0,0,0],[0,0],[0]],[[3972354960,98238384,-205488],[98238384,-1051680],[-205488]],[[0,0,0],[0,0],[0]],[[6088373280,50045856,-76128],[50045856,-346032],[-76128]],[[0,0,0],[0,0],[0]],[[6809349696,9452688,-13872],[9452688,-58848],[-13872]],[[0,0,0],[0,0],[0]],[[5617140816,-5536848,-1008],[-5536848,-4080],[-1008]],[[0,0],[0]],[[3400076352,-4930464],[-4930464]],[[0,0],[0]],[[1466162304,-1809024],[-1809024]],[[0,0],[0]],[[410464128,-372000],[-372000]],[[0,0],[0]],[[47127696,-41856],[-41856]],[[0,0],[0]],[[-15603696,-2016],[-2016]],[[0]],[[-9326880]],[[0]],[[-2344704]],[[0]],[[-341232]],[[0]],[[-27984]],[[0]],[[-1008]]]
theorem step099 : p099=NestedHorner.add p096 p098 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_plus e099 e096 e098 p096 p098 p099 rfl h096 h098 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
