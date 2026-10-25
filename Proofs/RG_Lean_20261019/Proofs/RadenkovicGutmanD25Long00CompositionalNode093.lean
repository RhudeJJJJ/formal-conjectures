/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD25Long00CompositionalNode033
import Proofs.RadenkovicGutmanD25Long00CompositionalNode064
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e093 : NestedArithmetic.Expr 3 := .times e033 e064
noncomputable def p093 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0,625]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,15000],[0,15000,50]],[[0,0,0],[0,0,0],[0,0]],[[-50625,-33750,84375],[-33750,326250,47150],[84375,47150]],[[0,0,0],[0,0,0],[0,0]],[[-1387800,1282500,510300],[1282500,1943700,49900],[510300,49900]],[[0,0,0],[0,0,0],[0,0]],[[-5959575,12582900,1281600],[12582900,4795150,20950],[1281600,20950]],[[0,0,0],[0,0,0],[0,0]],[[14290350,50329450,1744850],[50329450,6406900,3300],[1744850,3300]],[[0,0,0],[0,0,0],[0,0]],[[205113125,115932300,1408750],[115932300,5080000,100],[1408750,100]],[[0,0,0],[0,0],[0]],[[850822400,173435500,693050],[173435500,2459700],[693050]],[[0,0,0],[0,0],[0]],[[2099581450,178277000,205000],[178277000,718750],[205000]],[[0,0,0],[0,0],[0]],[[3558036200,129403450,34150],[129403450,119100],[34150]],[[0,0,0],[0,0],[0]],[[4394776850,66977350,2675],[66977350,9450],[2675]],[[0,0,0],[0,0],[0]],[[4078168100,24613650,50],[24613650,200],[50]],[[0,0],[0]],[[2888331600,6298000],[6298000]],[[0,0],[0]],[[1571672600,1076500],[1076500]],[[0,0],[0]],[[656706625,113300],[113300]],[[0,0],[0]],[[209119800,6150],[6150]],[[0,0],[0]],[[49950450,100],[100]],[[0]],[[8706400]],[[0]],[[1057025]],[[0]],[[82300]],[[0]],[[3475]],[[0]],[[50]]]
theorem step093 : p093=NestedArithmetic.mul p033 p064 := by decide +kernel
#print axioms step093
theorem h093 : NestedArithmetic.compile e093=p093 := StagedExprCompile.compile_times e093 e033 e064 p033 p064 p093 rfl h033 h064 step093
#print axioms h093
end Gebendorfer.RadenkovicGutman.FixedDegree25Long00Compositional
