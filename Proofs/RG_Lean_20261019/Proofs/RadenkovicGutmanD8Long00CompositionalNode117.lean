/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD8Long00CompositionalNode112
import Proofs.RadenkovicGutmanD8Long00CompositionalNode116
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e117 : NestedArithmetic.Expr 3 := .plus e112 e116
noncomputable def p117 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,192],[0,192,176]],[[0,0,0],[0,0,0],[0,0,0]],[[0,1728,4032],[1728,7200,4192],[4032,4192,4]],[[0,0,0],[0,0,0],[0,0]],[[60912,114912,48048],[114912,114888,10376],[48048,10376]],[[0,0,0],[0,0,0],[0,0]],[[1711908,1401768,189700],[1401768,496544,9408],[189700,9408]],[[0,0,0],[0,0,0],[0,0]],[[18336456,7344856,371904],[7344856,1035400,3504],[371904,3504]],[[0,0,0],[0,0,0],[0,0]],[[105638316,21719032,417904],[21719032,1234832,480],[417904,480]],[[0,0,0],[0,0,0],[0,0]],[[382489112,40945504,285856],[40945504,898976,8],[285856,8]],[[0,0,0],[0,0],[0]],[[948031028,52456120,121112],[52456120,406096],[121112]],[[0,0,0],[0,0],[0]],[[1693912560,47294936,31168],[47294936,111432],[31168]],[[0,0,0],[0,0],[0]],[[2254961112,30542672,4528],[30542672,17232],[4528]],[[0,0,0],[0,0],[0]],[[2284636296,14193824,304],[14193824,1224],[304]],[[0,0,0],[0,0],[0]],[[1785180288,4710776,4],[4710776,16],[4]],[[0,0],[0]],[[1083427904,1091656],[1091656]],[[0,0],[0]],[[511548512,168760],[168760]],[[0,0],[0]],[[187198952,15904],[15904]],[[0,0],[0]],[[52565076,744],[744]],[[0,0],[0]],[[11121104,8],[8]],[[0]],[[1719544]],[[0]],[[184584]],[[0]],[[12532]],[[0]],[[440]],[[0]],[[4]]]
theorem step117 : p117=NestedHorner.add p112 p116 := by decide +kernel
#print axioms step117
theorem h117 : NestedArithmetic.compile e117=p117 := StagedExprCompile.compile_plus e117 e112 e116 p112 p116 p117 rfl h112 h116 step117
#print axioms h117
end Gebendorfer.RadenkovicGutman.FixedDegree08Long00Compositional
