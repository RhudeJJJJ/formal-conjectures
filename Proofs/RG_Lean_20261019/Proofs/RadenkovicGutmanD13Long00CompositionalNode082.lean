/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD13Long00CompositionalNode078
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e082 : NestedArithmetic.Expr 3 := .scaled (-1) e078
noncomputable def p082 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,-169]],[[0,0],[0,0,0],[0,0]],[[0,0,-1521],[0,-3042,-3042],[-1521,-3042]],[[0,0,0],[0,0,0],[0,0]],[[13689,-50193,-26871],[-50193,-81120,-8112],[-26871,-8112]],[[0,0,0],[0,0,0],[0,0]],[[-173394,-807651,-117793],[-807651,-381602,-7436],[-117793,-7436]],[[0,0,0],[0,0,0],[0,0]],[[-4886973,-4652739,-241670],[-4652739,-811876,-2704],[-241670,-2704]],[[0,0,0],[0,0,0],[0,0]],[[-37660974,-14322074,-277836],[-14322074,-961272,-338],[-277836,-338]],[[0,0,0],[0,0],[0]],[[-156703391,-27425827,-191984],[-27425827,-683436],[-191984]],[[0,0,0],[0,0],[0]],[[-420184700,-35207263,-81289],[-35207263,-297778],[-81289]],[[0,0,0],[0,0],[0]],[[-788501610,-31532020,-20618],[-31532020,-77740],[-20618]],[[0,0,0],[0,0],[0]],[[-1084543642,-20099339,-2873],[-20099339,-11154],[-2873]],[[0,0,0],[0,0],[0]],[[-1124216730,-9169433,-169],[-9169433,-676],[-169]],[[0,0],[0]],[[-892972340,-2970344],[-2970344]],[[0,0],[0]],[[-548325570,-666705],[-666705]],[[0,0],[0]],[[-260925522,-98527],[-98527]],[[0,0],[0]],[[-95873531,-8619],[-8619]],[[0,0],[0]],[[-26917644,-338],[-338]],[[0]],[[-5663190]],[[0]],[[-863590]],[[0]],[[-90077]],[[0]],[[-5746]],[[0]],[[-169]]]
theorem step082 : p082=NestedHorner.scale (-1) p078 := by decide +kernel
#print axioms step082
theorem h082 : NestedArithmetic.compile e082=p082 := StagedExprCompile.compile_scaled (-1) e082 e078 p078 p082 rfl h078 step082
#print axioms h082
end Gebendorfer.RadenkovicGutman.FixedDegree13Long00Compositional
