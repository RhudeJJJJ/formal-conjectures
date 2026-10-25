/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD9Long00CompositionalNode035
import Proofs.RadenkovicGutmanD9Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-243],[0,-243]],[[0,0,0],[0,0,0],[0,0]],[[0,-2187,-2187],[-2187,-8748,-1053],[-2187,-1053]],[[0,0,0],[0,0,0],[0,0]],[[-39366,-87480,-15309],[-87480,-61236,-1296],[-15309,-1296]],[[0,0,0],[0,0,0],[0,0]],[[-971028,-729000,-42282],[-729000,-169128,-567],[-42282,-567]],[[0,0,0],[0,0,0],[0,0]],[[-8678016,-2884734,-61317],[-2884734,-245268,-81],[-61317,-81]],[[0,0,0],[0,0],[0]],[[-42144948,-6741306,-51516],[-6741306,-206064],[-51516]],[[0,0,0],[0,0],[0]],[[-130341798,-10248768,-25839],[-10248768,-103356],[-25839]],[[0,0,0],[0,0],[0]],[[-278554464,-10653930,-7614],[-10653930,-30456],[-7614]],[[0,0,0],[0,0],[0]],[[-431442936,-7766037,-1215],[-7766037,-4860],[-1215]],[[0,0,0],[0,0],[0]],[[-498734334,-4004397,-81],[-4004397,-324],[-81]],[[0,0],[0]],[[-438083154,-1452249],[-1452249]],[[0,0],[0]],[[-295327134,-362070],[-362070]],[[0,0],[0]],[[-153316800,-59049],[-59049]],[[0,0],[0]],[[-61121952,-5670],[-5670]],[[0,0],[0]],[[-18530370,-243],[-243]],[[0]],[[-4192236]],[[0]],[[-684936]],[[0]],[[-76302]],[[0]],[[-5184]],[[0]],[[-162]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree09Long00Compositional
