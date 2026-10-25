/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode043
import Proofs.RadenkovicGutmanD34Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e067 : NestedArithmetic.Expr 3 := .times e043 e061
noncomputable def p067 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,10404],[0,20808,-13056],[10404,-13056,4096]],[[0,0,0],[0,0,0],[0,0]],[[0,350676,-27336],[350676,-274704,17152],[-27336,17152]],[[0,0,0],[0,0,0],[0,0]],[[2369736,896724,-184412],[896724,-1220536,126976],[-184412,126976]],[[0,0,0],[0,0,0],[0,0]],[[12732552,-4295556,27176],[-4295556,-509232,149760],[27176,149760]],[[0,0,0],[0,0,0],[0,0]],[[-19006920,-21807944,1200112],[-21807944,4536032,61184],[1200112,61184]],[[0,0,0],[0,0,0],[0,0]],[[-357015744,-29499524,2436328],[-29499524,9906128,8192],[2436328,8192]],[[0,0,0],[0,0],[0]],[[-1419196416,18954132,2334404],[18954132,9566344],[2334404]],[[0,0,0],[0,0],[0]],[[-3088546864,118124048,1245496],[118124048,5084400],[1245496]],[[0,0,0],[0,0],[0]],[[-4154753512,187509052,378244],[187509052,1533960],[378244]],[[0,0,0],[0,0],[0]],[[-3303995144,170890612,61184],[170890612,246400],[61184]],[[0,0,0],[0,0],[0]],[[-844237440,101320136,4096],[101320136,16384],[4096]],[[0,0],[0]],[[1424024040,40419860],[40419860]],[[0,0],[0]],[[2183059624,10794588],[10794588]],[[0,0],[0]],[[1670882800,1853596],[1853596]],[[0,0],[0]],[[849266592,185216],[185216]],[[0,0],[0]],[[305317056,8192],[8192]],[[0]],[[78470280]],[[0]],[[14162520]],[[0]],[[1709208]],[[0]],[[124032]],[[0]],[[4096]]]
theorem step067 : p067=NestedArithmetic.mul p043 p061 := by decide +kernel
#print axioms step067
theorem h067 : NestedArithmetic.compile e067=p067 := StagedExprCompile.compile_times e067 e043 e061 p043 p061 p067 rfl h043 h061 step067
#print axioms h067
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
