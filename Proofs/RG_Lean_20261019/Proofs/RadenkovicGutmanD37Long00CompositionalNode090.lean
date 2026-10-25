/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD37Long00CompositionalNode035
import Proofs.RadenkovicGutmanD37Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e090 : NestedArithmetic.Expr 3 := .times e035 e064
noncomputable def p090 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-4107],[0,-4107]],[[0,0,0],[0,0,0],[0,0]],[[0,-36963,-61605],[-36963,-197136,-18019],[-61605,-18019]],[[0,0,0],[0,0,0],[0,0]],[[-665334,-2293704,-474303],[-2293704,-1470084,-22866],[-474303,-22866]],[[0,0,0],[0,0,0],[0,0]],[[-23100876,-21493818,-1454174],[-21493818,-4365556,-10767],[-1454174,-10767]],[[0,0,0],[0,0,0],[0,0]],[[-238485276,-92865412,-2328965],[-92865412,-6807852,-1887],[-2328965,-1887]],[[0,0,0],[0,0,0],[0,0]],[[-1274526864,-234168930,-2142374],[-234168930,-6138152,-74],[-2142374,-74]],[[0,0,0],[0,0],[0]],[[-4247890302,-381229130,-1168275],[-381229130,-3304100],[-1168275]],[[0,0,0],[0,0],[0]],[[-9669407876,-421985148,-374070],[-421985148,-1052724],[-374070]],[[0,0,0],[0,0],[0]],[[-15831905728,-326176201,-65823],[-326176201,-186628],[-65823]],[[0,0,0],[0,0],[0]],[[-19245323338,-177884493,-5217],[-177884493,-15392],[-5217]],[[0,0,0],[0,0],[0]],[[-17710988986,-68202581,-74],[-68202581,-296],[-74]],[[0,0],[0]],[[-12476816546,-18031284],[-18031284]],[[0,0],[0]],[[-6758257200,-3149551],[-3149551]],[[0,0],[0]],[[-2809929332,-333222],[-333222]],[[0,0],[0]],[[-889322602,-17501],[-17501]],[[0,0],[0]],[[-210697240,-222],[-222]],[[0]],[[-36302624]],[[0]],[[-4330258]],[[0]],[[-327080]],[[0]],[[-12950]],[[0]],[[-148]]]
theorem step090 : p090=NestedArithmetic.mul p035 p064 := by decide +kernel
#print axioms step090
theorem h090 : NestedArithmetic.compile e090=p090 := StagedExprCompile.compile_times e090 e035 e064 p035 p064 p090 rfl h035 h064 step090
#print axioms h090
end Gebendorfer.RadenkovicGutman.FixedDegree37Long00Compositional
