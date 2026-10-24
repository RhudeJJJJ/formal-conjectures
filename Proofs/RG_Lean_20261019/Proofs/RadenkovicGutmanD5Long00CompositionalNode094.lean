/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD5Long00CompositionalNode035
import Proofs.RadenkovicGutmanD5Long00CompositionalNode061
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e094 : NestedArithmetic.Expr 3 := .times e035 e061
noncomputable def p094 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0,0]],[[0,0,-225],[0,-450,90],[-225,90]],[[0,0,0],[0,0,0],[0,0]],[[0,-6615,-1140],[-6615,-660,390],[-1140,390]],[[0,0,0],[0,0,0],[0,0]],[[-46170,-50625,-955],[-50625,9430,480],[-955,480]],[[0,0,0],[0,0,0],[0,0]],[[-470610,-126675,4210],[-126675,39740,210],[4210,210]],[[0,0,0],[0,0,0],[0,0]],[[-1847070,-5330,11610],[-5330,68640,30],[11610,30]],[[0,0,0],[0,0],[0]],[[-2711160,653705,12830],[653705,63820],[12830]],[[0,0,0],[0,0],[0]],[[4059840,1672415,7545],[1672415,34230],[7545]],[[0,0,0],[0,0],[0]],[[27515420,2255000,2470],[2255000,10580],[2470]],[[0,0,0],[0,0],[0]],[[64633530,1934835,425],[1934835,1750],[425]],[[0,0,0],[0,0],[0]],[[94767470,1117885,30],[1117885,120],[30]],[[0,0],[0]],[[97559820,441220],[441220]],[[0,0],[0]],[[73795970,117475],[117475]],[[0,0],[0]],[[41838550,20195],[20195]],[[0,0],[0]],[[17887060,2025],[2025]],[[0,0],[0]],[[5740800,90],[90]],[[0]],[[1361880]],[[0]],[[231630]],[[0]],[[26710]],[[0]],[[1870]],[[0]],[[60]]]
theorem step094 : p094=NestedArithmetic.mul p035 p061 := by decide +kernel
#print axioms step094
theorem h094 : NestedArithmetic.compile e094=p094 := StagedExprCompile.compile_times e094 e035 e061 p035 p061 p094 rfl h035 h061 step094
#print axioms h094
end Gebendorfer.RadenkovicGutman.FixedDegree05Long00Compositional
