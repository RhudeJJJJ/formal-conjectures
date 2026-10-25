/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD14Long00CompositionalNode115
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e116 : NestedArithmetic.Expr 3 := .scaled (-1) e115
noncomputable def p116 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,-196]],[[0,0],[0,0,0],[0,0]],[[0,0,-1764],[0,0,-3528],[-1764,-3528]],[[0,0,0],[0,0,0],[0,0]],[[-15876,-31752,-31164],[-31752,-63504,-9408],[-31164,-9408]],[[0,0,0],[0,0,0],[0,0]],[[-560952,-645624,-136612],[-645624,-338688,-8624],[-136612,-8624]],[[0,0,0],[0,0,0],[0,0]],[[-7414092,-4032504,-280280],[-4032504,-762048,-3136],[-280280,-3136]],[[0,0,0],[0,0,0],[0,0]],[[-48487656,-13001856,-322224],[-13001856,-940800,-392],[-322224,-392]],[[0,0,0],[0,0],[0]],[[-190147636,-25766552,-222656],[-25766552,-694624],[-222656]],[[0,0,0],[0,0],[0]],[[-497185360,-34055000,-94276],[-34055000,-313600],[-94276]],[[0,0,0],[0,0],[0]],[[-922482232,-31320016,-23912],[-31320016,-84672],[-23912]],[[0,0,0],[0,0],[0]],[[-1262353288,-20468672,-3332],[-20468672,-12544],[-3332]],[[0,0,0],[0,0],[0]],[[-1305617152,-9562840,-196],[-9562840,-784],[-196]],[[0,0],[0]],[[-1036118720,-3169320],[-3169320]],[[0,0],[0]],[[-636012160,-727160],[-727160]],[[0,0],[0]],[[-302620472,-109760],[-109760]],[[0,0],[0]],[[-111190996,-9800],[-9800]],[[0,0],[0]],[[-31218096,-392],[-392]],[[0]],[[-6567960]],[[0]],[[-1001560]],[[0]],[[-104468]],[[0]],[[-6664]],[[0]],[[-196]]]
theorem step116 : p116=NestedHorner.scale (-1) p115 := by decide +kernel
#print axioms step116
theorem h116 : NestedArithmetic.compile e116=p116 := StagedExprCompile.compile_scaled (-1) e116 e115 p115 p116 rfl h115 step116
#print axioms h116
end Gebendorfer.RadenkovicGutman.FixedDegree14Long00Compositional
