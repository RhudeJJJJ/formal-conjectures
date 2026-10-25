/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD42Long00CompositionalNode221
import Proofs.RadenkovicGutmanD42Long00CompositionalNode003
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e222 : NestedArithmetic.Expr 3 := .times e221 e003
noncomputable def p222 : NestedHorner.Poly 3 := [[[],[],[]],[[0],[0],[0]],[[3528,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[109368,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[1555848,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[13462848,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[79189488,0,0],[0,0],[0]],[[0,0,0],[0,0],[0]],[[335209392,5292,0],[5292,0],[0]],[[0,0,0],[0,0],[0]],[[1054550952,118188,0],[118188,0],[0]],[[0,0,0],[0,0],[0]],[[2510838792,1173060,0],[1173060,0],[0]],[[0,0,0],[0,0],[0]],[[4564752192,6819624,0],[6819624,0],[0]],[[0,0,0],[0,0],[0]],[[6346797912,25770276,0],[25770276,0],[0]],[[0,0,0],[0,0],[0]],[[6714500184,66430476,1764],[66430476,3528],[1764]],[[0,0,0],[0,0],[0]],[[5338068624,119309904,24696],[119309904,49392],[24696]],[[0,0,0],[0,0],[0]],[[3119803344,149828868,142884],[149828868,285768],[142884]],[[0,0,0],[0,0],[0]],[[1292687424,130047372,441000],[130047372,882000],[441000]],[[0,0,0],[0,0],[0]],[[357114744,75763800,783216],[75763800,1566432],[783216]],[[0,0,0],[0,0],[0]],[[58582440,27989388,807912],[27989388,1615824],[807912]],[[0,0,0],[0,0],[0]],[[4286520,5858244,467460],[5858244,934920],[467460]],[[0,0,0],[0,0],[0]],[[0,523908,137592],[523908,275184],[137592]],[[0,0,0],[0,0],[0]],[[0,0,15876],[0,31752],[15876]]]
theorem step222 : p222=NestedArithmetic.mul p221 p003 := by decide +kernel
#print axioms step222
theorem h222 : NestedArithmetic.compile e222=p222 := StagedExprCompile.compile_times e222 e221 e003 p221 p003 p222 rfl h221 h003 step222
#print axioms h222
end Gebendorfer.RadenkovicGutman.FixedDegree42Long00Compositional
