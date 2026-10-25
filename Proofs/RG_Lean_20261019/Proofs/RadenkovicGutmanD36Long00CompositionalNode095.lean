/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode093
import Proofs.RadenkovicGutmanD36Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1296]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-11664],[0,-23328,38448],[-11664,38448,72]],[[0,0,0],[0,0,0],[0,0]],[[-104976,-388800,139968],[-388800,738720,129024],[139968,129024]],[[0,0,0],[0,0,0],[0,0]],[[-4834728,999216,1174824],[999216,5184000,141120],[1174824,141120]],[[0,0,0],[0,0,0],[0,0]],[[-26006832,27514080,3328128],[27514080,13812768,59184],[3328128,59184]],[[0,0,0],[0,0,0],[0,0]],[[29667384,135513504,4865040],[135513504,19423872,8784],[4865040,8784]],[[0,0,0],[0,0,0],[0,0]],[[748660752,347265360,4116096],[347265360,15961536,144],[4116096,144]],[[0,0,0],[0,0],[0]],[[3405224376,556492464,2084976],[556492464,7901856],[2084976]],[[0,0,0],[0,0],[0]],[[8827643808,600095376,624384],[600095376,2323872],[624384]],[[0,0,0],[0,0],[0]],[[15432064272,450463680,102816],[450463680,377568],[102816]],[[0,0,0],[0,0],[0]],[[19440198720,238398048,7488],[238398048,27360],[7488]],[[0,0,0],[0,0],[0]],[[18245882880,88662672,72],[88662672,288],[72]],[[0,0],[0]],[[12984575328,22705920],[22705920]],[[0,0],[0]],[[7060128480,3826080],[3826080]],[[0,0],[0]],[[2932738704,386064],[386064]],[[0,0],[0]],[[923527800,18576],[18576]],[[0,0],[0]],[[216761184,144],[144]],[[0]],[[36790992]],[[0]],[[4283568]],[[0]],[[309816]],[[0]],[[11088]],[[0]],[[72]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
