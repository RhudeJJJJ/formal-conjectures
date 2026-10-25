/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD6Long00CompositionalNode096
import Proofs.RadenkovicGutmanD6Long00CompositionalNode098
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e099 : NestedArithmetic.Expr 3 := .plus e096 e098
noncomputable def p099 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,216],[0,216,-48]],[[0,0,0],[0,0,0],[0,0]],[[0,0,2592],[0,9180,108],[2592,108]],[[0,0,0],[0,0,0],[0,0]],[[10692,75168,15660],[75168,52236,-996],[15660,-996]],[[0,0,0],[0,0,0],[0,0]],[[688824,699516,38196],[699516,116868,-1416],[38196,-1416]],[[0,0,0],[0,0,0],[0,0]],[[7633764,2855844,47088],[2855844,124716,-612],[47088,-612]],[[0,0,0],[0,0,0],[0,0]],[[41186844,6729780,29244],[6729780,52872,-84],[29244,-84]],[[0,0,0],[0,0],[0]],[[136164192,10139700,6072],[10139700,-14040],[6072]],[[0,0,0],[0,0],[0]],[[304923756,10213092,-2772],[10213092,-24780],[-2772]],[[0,0,0],[0,0],[0]],[[488006280,6961344,-1968],[6961344,-10692],[-1968]],[[0,0,0],[0,0],[0]],[[575651508,3149628,-444],[3149628,-2076],[-444]],[[0,0,0],[0,0],[0]],[[509156796,872880,-36],[872880,-156],[-36]],[[0,0],[0]],[[340102488,103128],[103128]],[[0,0],[0]],[[171202704,-17124],[-17124]],[[0,0],[0]],[[64073748,-8544],[-8544]],[[0,0],[0]],[[17257848,-1284],[-1284]],[[0,0],[0]],[[3095532,-72],[-72]],[[0]],[[284040]],[[0]],[[-12804]],[[0]],[[-7224]],[[0]],[[-840]],[[0]],[[-36]]]
theorem step099 : p099=NestedHorner.add p096 p098 := by decide +kernel
#print axioms step099
theorem h099 : NestedArithmetic.compile e099=p099 := StagedExprCompile.compile_plus e099 e096 e098 p096 p098 p099 rfl h096 h098 step099
#print axioms h099
end Gebendorfer.RadenkovicGutman.FixedDegree06Long00Compositional
