/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode097
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e098 : NestedArithmetic.Expr 3 := .scaled (-1) e097
noncomputable def p098 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,108],[0,108]],[[0,0,0],[0,0,0],[0,0]],[[0,-972,1620],[-972,4860,504],[1620,504]],[[0,0,0],[0,0,0],[0,0]],[[-14580,32400,12744],[32400,36828,732],[12744,732]],[[0,0,0],[0,0,0],[0,0]],[[87480,401436,40140],[401436,111924,444],[40140,444]],[[0,0,0],[0,0,0],[0,0]],[[2559924,1919772,66492],[1919772,180348,120],[66492,120]],[[0,0,0],[0,0,0],[0,0]],[[17987292,5150892,63948],[5150892,170376,12],[63948,12]],[[0,0,0],[0,0],[0]],[[68949576,8805924,37116],[8805924,98136],[37116]],[[0,0,0],[0,0],[0]],[[171916620,10192092,13044],[10192092,34596],[13044]],[[0,0,0],[0,0],[0]],[[301346184,8238636,2676],[8238636,7212],[2676]],[[0,0,0],[0,0],[0]],[[387410796,4715112,288],[4715112,804],[288]],[[0,0,0],[0,0],[0]],[[374484948,1911132,12],[1911132,36],[12]],[[0,0],[0]],[[276095808,541248],[541248]],[[0,0],[0]],[[156305808,103752],[103752]],[[0,0],[0]],[[67973508,12648],[12648]],[[0,0],[0]],[[22570416,864],[864]],[[0,0],[0]],[[5645340,24],[24]],[[0]],[[1038600]],[[0]],[[135060]],[[0]],[[11592]],[[0]],[[576]],[[0]],[[12]]]
theorem step098 : p098=NestedHorner.scale (-1) p097 := by decide +kernel
#print axioms step098
theorem h098 : NestedArithmetic.compile e098=p098 := StagedExprCompile.compile_scaled (-1) e098 e097 p097 p098 rfl h097 step098
#print axioms h098
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
