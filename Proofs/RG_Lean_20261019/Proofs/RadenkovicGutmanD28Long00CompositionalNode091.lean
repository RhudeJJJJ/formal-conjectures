/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD28Long00CompositionalNode090
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e091 : NestedArithmetic.Expr 3 := .scaled (-1) e090
noncomputable def p091 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2352],[0,2352]],[[0,0,0],[0,0,0],[0,0]],[[0,21168,35280],[21168,112896,10360],[35280,10360]],[[0,0,0],[0,0,0],[0,0]],[[381024,1313928,271992],[1313928,843360,13272],[271992,13272]],[[0,0,0],[0,0,0],[0,0]],[[13236048,12323808,835352],[12323808,2510368,6384],[835352,6384]],[[0,0,0],[0,0,0],[0,0]],[[136739232,53304832,1340864],[53304832,3927168,1176],[1340864,1176]],[[0,0,0],[0,0,0],[0,0]],[[731356416,134589168,1237208],[134589168,3556448,56],[1237208,56]],[[0,0,0],[0,0],[0]],[[2439772608,219456272,677712],[219456272,1926848],[677712]],[[0,0,0],[0,0],[0]],[[5559403472,243386304,218568],[243386304,620256],[218568]],[[0,0,0],[0,0],[0]],[[9113472256,188586496,38976],[188586496,112000],[38976]],[[0,0,0],[0,0],[0]],[[11093981920,103177032,3192],[103177032,9632],[3192]],[[0,0,0],[0,0],[0]],[[10226614384,39731720,56],[39731720,224],[56]],[[0,0],[0]],[[7218904784,10570392],[10570392]],[[0,0],[0]],[[3919988688,1864576],[1864576]],[[0,0],[0]],[[1634975552,200760],[200760]],[[0,0],[0]],[[519576736,10976],[10976]],[[0,0],[0]],[[123778480,168],[168]],[[0]],[[21494816]],[[0]],[[2595040]],[[0]],[[200144]],[[0]],[[8288]],[[0]],[[112]]]
theorem step091 : p091=NestedHorner.scale (-1) p090 := by decide +kernel
#print axioms step091
theorem h091 : NestedArithmetic.compile e091=p091 := StagedExprCompile.compile_scaled (-1) e091 e090 p090 p091 rfl h090 step091
#print axioms h091
end Gebendorfer.RadenkovicGutman.FixedDegree28Long00Compositional
