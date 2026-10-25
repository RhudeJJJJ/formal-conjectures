/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode093
import Proofs.RadenkovicGutmanD42Long00CompositionalNode094
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e095 : NestedArithmetic.Expr 3 := .plus e093 e094
noncomputable def p095 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1764]],[[0,0],[0,0,0],[0,0,0]],[[0,0,-15876],[0,-31752,52416],[-15876,52416,84]],[[0,0,0],[0,0,0],[0,0]],[[-142884,-528444,191268],[-528444,1008504,175728],[191268,175728]],[[0,0,0],[0,0,0],[0,0]],[[-6565860,1390284,1603224],[1390284,7072632,191856],[1603224,191856]],[[0,0,0],[0,0,0],[0,0]],[[-35042868,37681308,4538520],[37681308,18834984,80136],[4538520,80136]],[[0,0,0],[0,0,0],[0,0]],[[43440516,185282832,6629448],[185282832,26468400,11760],[6629448,11760]],[[0,0,0],[0,0,0],[0,0]],[[1033293492,474411924,5603472],[474411924,21729456,168],[5603472,168]],[[0,0,0],[0,0],[0]],[[4677223236,759751020,2834412],[759751020,10741416],[2834412]],[[0,0,0],[0,0],[0]],[[12101646648,818751864,846888],[818751864,3151176],[846888]],[[0,0,0],[0,0],[0]],[[21130940880,614150460,138852],[614150460,509544],[138852]],[[0,0,0],[0,0],[0]],[[26596118304,324732660,9996],[324732660,36456],[9996]],[[0,0,0],[0,0],[0]],[[24943351104,120626688,84],[120626688,336],[84]],[[0,0],[0]],[[17737792296,30838500],[30838500]],[[0,0],[0]],[[9637121592,5182212],[5182212]],[[0,0],[0]],[[3999666132,520212],[520212]],[[0,0],[0]],[[1258147716,24696],[24696]],[[0,0],[0]],[[294883848,168],[168]],[[0]],[[49951104]],[[0]],[[5797596]],[[0]],[[416892]],[[0]],[[14700]],[[0]],[[84]]]
theorem step095 : p095=NestedHorner.add p093 p094 := by decide +kernel
#print axioms step095
theorem h095 : NestedArithmetic.compile e095=p095 := StagedExprCompile.compile_plus e095 e093 e094 p093 p094 p095 rfl h093 h094 step095
#print axioms h095
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
