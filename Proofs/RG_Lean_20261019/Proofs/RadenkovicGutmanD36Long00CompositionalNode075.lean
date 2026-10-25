/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD36Long00CompositionalNode033
import Proofs.RadenkovicGutmanD36Long00CompositionalNode053
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e075 : NestedArithmetic.Expr 3 := .times e033 e053
noncomputable def p075 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,1296]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,23328],[0,23328]],[[0,0,0],[0,0,0],[0,0]],[[-104976,0,104976],[0,419904,62208],[104976,62208]],[[0,0,0],[0,0,0],[0,0]],[[-1819584,1889568,559872],[1889568,2239488,57024],[559872,57024]],[[0,0,0],[0,0,0],[0,0]],[[-5563728,15116544,1259712],[15116544,5038848,20736],[1259712,20736]],[[0,0,0],[0,0,0],[0,0]],[[26438400,54167616,1555200],[54167616,6220800,2592],[1555200,2592]],[[0,0,0],[0,0],[0]],[[251972208,114773760,1148256],[114773760,4593024],[1148256]],[[0,0,0],[0,0],[0]],[[930144384,159913440,518400],[159913440,2073600],[518400]],[[0,0,0],[0,0],[0]],[[2124887904,154151424,139968],[154151424,559872],[139968]],[[0,0,0],[0,0],[0]],[[3383871552,105328512,20736],[105328512,82944],[20736]],[[0,0,0],[0,0],[0]],[[3958258752,51383808,1296],[51383808,5184],[1296]],[[0,0],[0]],[[3494187072,17768160],[17768160]],[[0,0],[0]],[[2360212992,4250880],[4250880]],[[0,0],[0]],[[1226171520,668736],[668736]],[[0,0],[0]],[[488943216,62208],[62208]],[[0,0],[0]],[[148241664,2592],[2592]],[[0]],[[33537888]],[[0]],[[5479488]],[[0]],[[610416]],[[0]],[[41472]],[[0]],[[1296]]]
theorem step075 : p075=NestedArithmetic.mul p033 p053 := by decide +kernel
#print axioms step075
theorem h075 : NestedArithmetic.compile e075=p075 := StagedExprCompile.compile_times e075 e033 e053 p033 p053 p075 rfl h033 h053 step075
#print axioms h075
end Gebendorfer.RadenkovicGutman.FixedDegree36Long00Compositional
