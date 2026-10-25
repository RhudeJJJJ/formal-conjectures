/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD20Long00CompositionalNode033
import Proofs.RadenkovicGutmanD20Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e079 : NestedArithmetic.Expr 3 := .times e033 e074
noncomputable def p079 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,1200],[0,1200]],[[0,0,0],[0,0,0],[0,0]],[[0,-10800,10800],[-10800,39600,5200],[10800,5200]],[[0,0,0],[0,0,0],[0,0]],[[-162000,118800,75600],[118800,271200,6400],[75600,6400]],[[0,0,0],[0,0,0],[0,0]],[[-1026000,1670400,208800],[1670400,729200,2800],[208800,2800]],[[0,0,0],[0,0,0],[0,0]],[[561600,7559600,302800],[7559600,1028000,400],[302800,400]],[[0,0,0],[0,0],[0]],[[26425200,18717600,254400],[18717600,840000],[254400]],[[0,0,0],[0,0],[0]],[[125611600,29404400,127600],[29404400,410400],[127600]],[[0,0,0],[0,0],[0]],[[332468000,31285600,37600],[31285600,118000],[37600]],[[0,0,0],[0,0],[0]],[[590136000,23251600,6000],[23251600,18400],[6000]],[[0,0,0],[0,0],[0]],[[753710000,12202800,400],[12202800,1200],[400]],[[0,0],[0]],[[716920000,4500000],[4500000]],[[0,0],[0]],[[516897600,1140000],[1140000]],[[0,0],[0]],[[284572800,188800],[188800]],[[0,0],[0]],[[119554000,18400],[18400]],[[0,0],[0]],[[38005200,800],[800]],[[0]],[[8978400]],[[0]],[[1526400]],[[0]],[[176400]],[[0]],[[12400]],[[0]],[[400]]]
theorem step079 : p079=NestedArithmetic.mul p033 p074 := by decide +kernel
#print axioms step079
theorem h079 : NestedArithmetic.compile e079=p079 := StagedExprCompile.compile_times e079 e033 e074 p033 p074 p079 rfl h033 h074 step079
#print axioms h079
end Gebendorfer.RadenkovicGutman.FixedDegree20Long00Compositional
