/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD35Long00CompositionalNode071
import Proofs.RadenkovicGutmanD35Long00CompositionalNode072
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e073 : NestedArithmetic.Expr 3 := .plus e071 e072
noncomputable def p073 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0,0]],[[0,-66150,0],[-66150,-13545,0],[0,0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1114155,-1246455,0],[-1246455,-162120,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-22796235,-10008810,0],[-10008810,-786485,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-206877510,-45425135,0],[-45425135,-2006340,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-1107789165,-130280150,0],[-130280150,-2944480,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-3928878555,-250327805,0],[-250327805,-2582930,0],[0,0]],[[0,0,0],[0,0],[0]],[[-9822459220,-333647370,0],[-333647370,-1364405],[0]],[[0,0,0],[0,0],[0]],[[-17988748680,-314971580,0],[-314971580,-423640],[0]],[[0,0,0],[0,0],[0]],[[-24748301795,-212826670,0],[-212826670,-71085],[0]],[[0,0,0],[0,0],[0]],[[-26006194060,-103029255,0],[-103029255,-4970],[0]],[[0,0,0],[0,0],[0]],[[-21091299670,-35375970,0],[-35375970,0],[0]],[[0,0],[0]],[[-13270638500,-8399125],[-8399125]],[[0,0],[0]],[[-6480478235,-1309910],[-1309910]],[[0,0],[0]],[[-2444345995,-120645],[-120645]],[[0,0],[0]],[[-704249980,-4970],[-4970]],[[0,0],[0]],[[-151942700,0],[0]],[[0]],[[-23740325]],[[0]],[[-2534875]],[[0]],[[-165375]],[[0]],[[-4970]],[[0]],[[0]]]
theorem step073 : p073=NestedHorner.add p071 p072 := by decide +kernel
#print axioms step073
theorem h073 : NestedArithmetic.compile e073=p073 := StagedExprCompile.compile_plus e073 e071 e072 p071 p072 p073 rfl h071 h072 step073
#print axioms h073
end Gebendorfer.RadenkovicGutman.FixedDegree35Long00Compositional
