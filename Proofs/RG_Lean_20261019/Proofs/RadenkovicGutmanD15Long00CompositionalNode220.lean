/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD15Long00CompositionalNode217
import Proofs.RadenkovicGutmanD15Long00CompositionalNode219
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e220 : NestedArithmetic.Expr 3 := .times e217 e219
noncomputable def p220 : NestedHorner.Poly 3 := [[[-450],[0],[0]],[[0,0],[0,0],[0]],[[-13950,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-198450,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-1717200,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-10100700,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[-42756300,-675,0],[-675,0],[0]],[[0,0,0],[0,0],[0]],[[-134509050,-15075,0],[-15075,0],[0]],[[0,0,0],[0,0],[0]],[[-320260050,-149625,0],[-149625,0],[0]],[[0,0,0],[0,0],[0]],[[-582238800,-869850,0],[-869850,0],[0]],[[0,0,0],[0,0],[0]],[[-809540550,-3287025,0],[-3287025,0],[0]],[[0,0,0],[0,0],[0]],[[-856441350,-8473275,-225],[-8473275,-450],[-225]],[[0,0,0],[0,0],[0]],[[-680876100,-15218100,-3150],[-15218100,-6300],[-3150]],[[0,0,0],[0,0],[0]],[[-397934100,-19110825,-18225],[-19110825,-36450],[-18225]],[[0,0,0],[0,0],[0]],[[-164883600,-16587675,-56250],[-16587675,-112500],[-56250]],[[0,0,0],[0,0],[0]],[[-45550350,-9663750,-99900],[-9663750,-199800],[-99900]],[[0,0,0],[0,0],[0]],[[-7472250,-3570075,-103050],[-3570075,-206100],[-103050]],[[0,0,0],[0,0],[0]],[[-546750,-747225,-59625],[-747225,-119250],[-59625]],[[0,0,0],[0,0],[0]],[[0,-66825,-17550],[-66825,-35100],[-17550]],[[0,0,0],[0,0],[0]],[[0,0,-2025],[0,-4050],[-2025]]]
theorem step220 : p220=NestedArithmetic.mul p217 p219 := by decide +kernel
#print axioms step220
theorem h220 : NestedArithmetic.compile e220=p220 := StagedExprCompile.compile_times e220 e217 e219 p217 p219 p220 rfl h217 h219 step220
#print axioms h220
end Gebendorfer.RadenkovicGutman.FixedDegree15Long00Compositional
