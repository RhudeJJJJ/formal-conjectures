/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD10Long00CompositionalNode089
import Proofs.RadenkovicGutmanD10Long00CompositionalNode091
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e092 : NestedArithmetic.Expr 3 := .plus e089 e091
noncomputable def p092 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,600],[0,600,-160]],[[0,0,0],[0,0,0],[0,0]],[[0,0,7200],[0,24300,-220],[7200,-220]],[[0,0,0],[0,0,0],[0,0]],[[21060,197640,40980],[197640,124920,-4220],[40980,-4220]],[[0,0,0],[0,0,0],[0,0]],[[1662660,1770120,92060],[1770120,235740,-5320],[92060,-5320]],[[0,0,0],[0,0,0],[0,0]],[[18422640,6938460,97920],[6938460,162680,-2220],[97920,-2220]],[[0,0,0],[0,0,0],[0,0]],[[98005020,15616920,39140],[15616920,-65440,-300],[39140,-300]],[[0,0,0],[0,0],[0]],[[318180380,22243420,-15240],[22243420,-185960],[-15240]],[[0,0,0],[0,0],[0]],[[698081120,20749960,-22620],[20749960,-130980],[-22620]],[[0,0,0],[0,0],[0]],[[1091849840,12527360,-9600],[12527360,-45400],[-9600]],[[0,0,0],[0,0],[0]],[[1254197300,4440220,-1860],[4440220,-7940],[-1860]],[[0,0,0],[0,0],[0]],[[1074135360,484760,-140],[484760,-560],[-140]],[[0,0],[0]],[[688158960,-329820],[-329820]],[[0,0],[0]],[[326634760,-182300],[-182300]],[[0,0],[0]],[[111388100,-42980],[-42980]],[[0,0],[0]],[[25112380,-5180],[-5180]],[[0,0],[0]],[[2672560,-260],[-260]],[[0]],[[-351760]],[[0]],[[-192660]],[[0]],[[-34620]],[[0]],[[-3140]],[[0]],[[-120]]]
theorem step092 : p092=NestedHorner.add p089 p091 := by decide +kernel
#print axioms step092
theorem h092 : NestedArithmetic.compile e092=p092 := StagedExprCompile.compile_plus e092 e089 e091 p089 p091 p092 rfl h089 h091 step092
#print axioms h092
end Gebendorfer.RadenkovicGutman.FixedDegree10Long00Compositional
