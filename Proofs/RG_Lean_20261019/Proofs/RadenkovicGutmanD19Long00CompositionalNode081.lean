/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD19Long00CompositionalNode079
import Proofs.RadenkovicGutmanD19Long00CompositionalNode080
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e081 : NestedArithmetic.Expr 3 := .plus e079 e080
noncomputable def p081 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[0,-19494,0],[-19494,-3249,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-321651,-282663,0],[-282663,-28158,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-5253633,-1741464,0],[-1741464,-95665,0],[0,0]],[[0,0,0],[0,0,0],[0,0]],[[-38169252,-6034115,0],[-6034115,-165338,0],[0,0]],[[0,0,0],[0,0],[0]],[[-163982445,-13151952,0],[-13151952,-160284],[0]],[[0,0,0],[0,0],[0]],[[-467541569,-19139137,0],[-19139137,-90250],[0]],[[0,0,0],[0,0],[0]],[[-941406414,-19247076,0],[-19247076,-29241],[0]],[[0,0,0],[0,0],[0]],[[-1390252876,-13627028,0],[-13627028,-5054],[0]],[[0,0,0],[0,0],[0]],[[-1542530979,-6833730,0],[-6833730,-361],[0]],[[0,0],[0]],[[-1305424374,-2411119],[-2411119]],[[0,0],[0]],[[-849710970,-584820],[-584820]],[[0,0],[0]],[[-426473848,-92777],[-92777]],[[0,0],[0]],[[-164510227,-8664],[-8664]],[[0,0],[0]],[[-48286277,-361],[-361]],[[0]],[[-10580910]],[[0]],[[-1675040]],[[0]],[[-180861]],[[0]],[[-11913]],[[0]],[[-361]]]
theorem step081 : p081=NestedHorner.add p079 p080 := by decide +kernel
#print axioms step081
theorem h081 : NestedArithmetic.compile e081=p081 := StagedExprCompile.compile_plus e081 e079 e080 p079 p080 p081 rfl h079 h080 step081
#print axioms h081
end Gebendorfer.RadenkovicGutman.FixedDegree19Long00Compositional
