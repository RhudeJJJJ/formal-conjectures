/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode096
import Proofs.RadenkovicGutmanD10Long00CompositionalNode098
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .plus e096 e098
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,600],[0,600,-160]],[[0,0,0],[0,0,0],[0,0]],[[0,0,7200],[0,25020,-220],[7200,-220]],[[0,0,0],[0,0,0],[0,0]],[[27540,204120,40980],[204120,130980,-4220],[40980,-4220]],[[0,0,0],[0,0,0],[0,0]],[[1831680,1841940,92060],[1841940,255380,-5320],[92060,-5320]],[[0,0,0],[0,0,0],[0,0]],[[20064780,7276500,97920],[7276500,194020,-2220],[97920,-2220]],[[0,0,0],[0,0,0],[0,0]],[[106663260,16509420,39140],[16509420,-39080,-300],[39140,-300]],[[0,0,0],[0,0],[0]],[[346939240,23714100,-15240],[23714100,-174840],[-15240]],[[0,0,0],[0,0],[0]],[[763082180,22335340,-22620],[22335340,-129500],[-22620]],[[0,0,0],[0,0],[0]],[[1196339000,13657840,-9600],[13657840,-45900],[-9600]],[[0,0,0],[0,0],[0]],[[1376710260,4958100,-1860],[4958100,-8140],[-1860]],[[0,0,0],[0,0],[0]],[[1180123700,618840,-140],[618840,-580],[-140]],[[0,0],[0]],[[755695480,-322840],[-322840]],[[0,0],[0]],[[357685200,-189700],[-189700]],[[0,0],[0]],[[121064500,-45520],[-45520]],[[0,0],[0]],[[26734960,-5540],[-5540]],[[0,0],[0]],[[2567940,-280],[-280]],[[0]],[[-495400]],[[0]],[[-233700]],[[0]],[[-40960]],[[0]],[[-3680]],[[0]],[[-140]]]
theorem step099 : p099=NestedHorner.add p096 p098 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_plus e099 e096 e098 p096 p098 p099 rfl h096 h098 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
