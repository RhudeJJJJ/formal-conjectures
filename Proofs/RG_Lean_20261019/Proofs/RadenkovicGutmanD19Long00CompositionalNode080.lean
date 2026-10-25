/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode035
import Proofs.RadenkovicGutmanD19Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-1083],[0,-1083]],[[0,0,0],[0,0,0],[0,0]],[[0,-9747,-9747],[-9747,-38988,-4693],[-9747,-4693]],[[0,0,0],[0,0,0],[0,0]],[[-175446,-389880,-68229],[-389880,-272916,-5776],[-68229,-5776]],[[0,0,0],[0,0,0],[0,0]],[[-4327668,-3249000,-188442],[-3249000,-753768,-2527],[-188442,-2527]],[[0,0,0],[0,0,0],[0,0]],[[-38676096,-12856654,-273277],[-12856654,-1093108,-361],[-273277,-361]],[[0,0,0],[0,0],[0]],[[-187831188,-30044586,-229596],[-30044586,-918384],[-229596]],[[0,0,0],[0,0],[0]],[[-580906038,-45676608,-115159],[-45676608,-460636],[-115159]],[[0,0,0],[0,0],[0]],[[-1241458784,-47482330,-33934],[-47482330,-135736],[-33934]],[[0,0,0],[0,0],[0]],[[-1922850616,-34611597,-5415],[-34611597,-21660],[-5415]],[[0,0,0],[0,0],[0]],[[-2222754254,-17846757,-361],[-17846757,-1444],[-361]],[[0,0],[0]],[[-1952444674,-6472369],[-6472369]],[[0,0],[0]],[[-1316211054,-1613670],[-1613670]],[[0,0],[0]],[[-683300800,-263169],[-263169]],[[0,0],[0]],[[-272407712,-25270],[-25270]],[[0,0],[0]],[[-82585970,-1083],[-1083]],[[0]],[[-18683916]],[[0]],[[-3052616]],[[0]],[[-340062]],[[0]],[[-23104]],[[0]],[[-722]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
