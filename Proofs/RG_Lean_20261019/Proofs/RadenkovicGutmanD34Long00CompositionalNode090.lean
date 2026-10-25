/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD34Long00CompositionalNode035
import Proofs.RadenkovicGutmanD34Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e090 : NestedArithmetic.Expr 3 := .times e035 e064
noncomputable def p090 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-3468],[0,-3468]],[[0,0,0],[0,0,0],[0,0]],[[0,-31212,-52020],[-31212,-166464,-15232],[-52020,-15232]],[[0,0,0],[0,0,0],[0,0]],[[-561816,-1936980,-400656],[-1936980,-1241952,-19380],[-400656,-19380]],[[0,0,0],[0,0,0],[0,0]],[[-19509336,-18155592,-1228964],[-18155592,-3690496,-9180],[-1228964,-9180]],[[0,0,0],[0,0,0],[0,0]],[[-201445920,-78466288,-1969484],[-78466288,-5760144,-1632],[-1969484,-1632]],[[0,0,0],[0,0,0],[0,0]],[[-1076816448,-197931408,-1813220],[-197931408,-5199824,-68],[-1813220,-68]],[[0,0,0],[0,0],[0]],[[-3589838184,-322373312,-990012],[-322373312,-2804048],[-990012]],[[0,0,0],[0,0],[0]],[[-8173835960,-357026928,-317628],[-357026928,-895968],[-317628]],[[0,0,0],[0,0],[0]],[[-13387611520,-276152284,-56100],[-276152284,-159664],[-56100]],[[0,0,0],[0,0],[0]],[[-16280349064,-150736416,-4488],[-150736416,-13328],[-4488]],[[0,0,0],[0,0],[0]],[[-14989319152,-57863648,-68],[-57863648,-272],[-68]],[[0,0],[0]],[[-10565392832,-15324684],[-15324684]],[[0,0],[0]],[[-5726855688,-2684164],[-2684164]],[[0,0],[0]],[[-2383173968,-285396],[-285396]],[[0,0],[0]],[[-755115112,-15164],[-15164]],[[0,0],[0]],[[-179176600,-204],[-204]],[[0]],[[-30939728]],[[0]],[[-3703144]],[[0]],[[-281384]],[[0]],[[-11288]],[[0]],[[-136]]]
theorem step090 : p090=NestedArithmetic.mul p035 p064 := by decide +kernel
#print axioms step090
theorem h090 : NestedArithmetic.compile e090=p090 := StagedExprCompile.compile_times e090 e035 e064 p035 p064 p090 rfl h035 h064 step090
#print axioms h090
end Gebendorfer.RadenkovicGutman.FixedDegree34Long00Compositional
