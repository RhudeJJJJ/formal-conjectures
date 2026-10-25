/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD18Long00CompositionalNode035
import Proofs.RadenkovicGutmanD18Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e080 : NestedArithmetic.Expr 3 := .times e035 e053
noncomputable def p080 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,-972],[0,-972]],[[0,0,0],[0,0,0],[0,0]],[[0,-8748,-8748],[-8748,-34992,-4212],[-8748,-4212]],[[0,0,0],[0,0,0],[0,0]],[[-157464,-349920,-61236],[-349920,-244944,-5184],[-61236,-5184]],[[0,0,0],[0,0,0],[0,0]],[[-3884112,-2916000,-169128],[-2916000,-676512,-2268],[-169128,-2268]],[[0,0,0],[0,0,0],[0,0]],[[-34712064,-11538936,-245268],[-11538936,-981072,-324],[-245268,-324]],[[0,0,0],[0,0],[0]],[[-168579792,-26965224,-206064],[-26965224,-824256],[-206064]],[[0,0,0],[0,0],[0]],[[-521367192,-40995072,-103356],[-40995072,-413424],[-103356]],[[0,0,0],[0,0],[0]],[[-1114217856,-42615720,-30456],[-42615720,-121824],[-30456]],[[0,0,0],[0,0],[0]],[[-1725771744,-31064148,-4860],[-31064148,-19440],[-4860]],[[0,0,0],[0,0],[0]],[[-1994937336,-16017588,-324],[-16017588,-1296],[-324]],[[0,0],[0]],[[-1752332616,-5808996],[-5808996]],[[0,0],[0]],[[-1181308536,-1448280],[-1448280]],[[0,0],[0]],[[-613267200,-236196],[-236196]],[[0,0],[0]],[[-244487808,-22680],[-22680]],[[0,0],[0]],[[-74121480,-972],[-972]],[[0]],[[-16768944]],[[0]],[[-2739744]],[[0]],[[-305208]],[[0]],[[-20736]],[[0]],[[-648]]]
theorem step080 : p080=NestedArithmetic.mul p035 p053 := by decide +kernel
#print axioms step080
theorem h080 : NestedArithmetic.compile e080=p080 := StagedExprCompile.compile_times e080 e035 e053 p035 p053 p080 rfl h035 h053 step080
#print axioms h080
end Gebendorfer.RadenkovicGutman.FixedDegree18Long00Compositional
