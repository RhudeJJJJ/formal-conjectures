/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD24Long00CompositionalNode043
import Proofs.RadenkovicGutmanD24Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,5184],[0,10368,-6336],[5184,-6336,1936]],[[0,0,0],[0,0,0],[0,0]],[[0,176256,-12096],[176256,-131904,7392],[-12096,7392]],[[0,0,0],[0,0,0],[0,0]],[[1206576,497664,-89712],[497664,-609216,59136],[-89712,59136]],[[0,0,0],[0,0,0],[0,0]],[[6901632,-1899936,-2304],[-1899936,-350272,70400],[-2304,70400]],[[0,0,0],[0,0,0],[0,0]],[[-5605200,-10636224,538752],[-10636224,1965952,28864],[538752,28864]],[[0,0,0],[0,0,0],[0,0]],[[-164848704,-15919104,1123968],[-15919104,4520448,3872],[1123968,3872]],[[0,0,0],[0,0],[0]],[[-685199696,4614272,1088224],[4614272,4435584],[1088224]],[[0,0,0],[0,0],[0]],[[-1533822464,50189408,583936],[50189408,2376640],[583936]],[[0,0,0],[0,0],[0]],[[-2133285152,83809792,177984],[83809792,720640],[177984]],[[0,0,0],[0,0],[0]],[[-1812089984,77965952,28864],[77965952,116160],[28864]],[[0,0,0],[0,0],[0]],[[-661330880,46765696,1936],[46765696,7744],[1936]],[[0,0],[0]],[[470536640,18800160],[18800160]],[[0,0],[0]],[[914502784,5048768],[5048768]],[[0,0],[0]],[[738499520,870656],[870656]],[[0,0],[0]],[[384613552,87296],[87296]],[[0,0],[0]],[[140244096,3872],[3872]],[[0]],[[36384480]],[[0]],[[6611200]],[[0]],[[801968]],[[0]],[[58432]],[[0]],[[1936]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree24Long00Compositional
