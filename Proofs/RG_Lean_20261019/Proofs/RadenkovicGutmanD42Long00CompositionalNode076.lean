/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode035
import Proofs.RadenkovicGutmanD42Long00CompositionalNode074
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e076 : NestedArithmetic.Expr 3 := .times e035 e074
noncomputable def p076 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,-15876],[0,-31752],[-15876]],[[0,0,0],[0,0],[0]],[[0,-523908,-137592],[-523908,-275184],[-137592]],[[0,0,0],[0,0],[0]],[[-4286520,-5858244,-467460],[-5858244,-934920],[-467460]],[[0,0,0],[0,0],[0]],[[-58582440,-27989388,-807912],[-27989388,-1615824],[-807912]],[[0,0,0],[0,0],[0]],[[-357114744,-75763800,-783216],[-75763800,-1566432],[-783216]],[[0,0,0],[0,0],[0]],[[-1292687424,-130047372,-441000],[-130047372,-882000],[-441000]],[[0,0,0],[0,0],[0]],[[-3119803344,-149828868,-142884],[-149828868,-285768],[-142884]],[[0,0,0],[0,0],[0]],[[-5338068624,-119309904,-24696],[-119309904,-49392],[-24696]],[[0,0,0],[0,0],[0]],[[-6714500184,-66430476,-1764],[-66430476,-3528],[-1764]],[[0,0],[0]],[[-6346797912,-25770276],[-25770276]],[[0,0],[0]],[[-4564752192,-6819624],[-6819624]],[[0,0],[0]],[[-2510838792,-1173060],[-1173060]],[[0,0],[0]],[[-1054550952,-118188],[-118188]],[[0,0],[0]],[[-335209392,-5292],[-5292]],[[0]],[[-79189488]],[[0]],[[-13462848]],[[0]],[[-1555848]],[[0]],[[-109368]],[[0]],[[-3528]]]
theorem step076 : p076=NestedArithmetic.mul p035 p074 := by decide +kernel
#print axioms step076
theorem h076 : NestedArithmetic.compile e076=p076 := StagedExprCompile.compile_times e076 e035 e074 p035 p074 p076 rfl h035 h074 step076
#print axioms h076
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
