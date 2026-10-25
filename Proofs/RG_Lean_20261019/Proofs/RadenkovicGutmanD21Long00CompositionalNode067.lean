/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD21Long00CompositionalNode043
import Proofs.RadenkovicGutmanD21Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,3969],[0,7938,-4788],[3969,-4788,1444]],[[0,0,0],[0,0,0],[0,0]],[[0,135513,-8694],[135513,-99126,5244],[-8694,5244]],[[0,0,0],[0,0,0],[0,0]],[[933444,400059,-67815],[400059,-466458,43776],[-67815,43776]],[[0,0,0],[0,0,0],[0,0]],[[5493528,-1362717,-7326],[-1362717,-302350,52364],[-7326,52364]],[[0,0,0],[0,0,0],[0,0]],[[-2825118,-8042088,391200],[-8042088,1399444,21508],[391200,21508]],[[0,0,0],[0,0,0],[0,0]],[[-121173306,-12591165,827994],[-12591165,3310812,2888],[827994,2888]],[[0,0,0],[0,0],[0]],[[-515704034,1837175,805981],[1837175,3275982],[805981]],[[0,0,0],[0,0],[0]],[[-1170493688,35335628,433750],[35335628,1762666],[433750]],[[0,0,0],[0,0],[0]],[[-1653161354,60711511,132453],[60711511,535846],[132453]],[[0,0,0],[0,0],[0]],[[-1444116344,57101105,21508],[57101105,86526],[21508]],[[0,0,0],[0,0],[0]],[[-590737700,34459264,1444],[34459264,5776],[1444]],[[0,0],[0]],[[275414630,13907985],[13907985]],[[0,0],[0]],[[638220250,3745637],[3745637]],[[0,0],[0]],[[531619142,647339],[647339]],[[0,0],[0]],[[280567630,65018],[65018]],[[0,0],[0]],[[103076004,2888],[2888]],[[0]],[[26872890]],[[0]],[[4899916]],[[0]],[[595940]],[[0]],[[43510]],[[0]],[[1444]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree21Long00Compositional
