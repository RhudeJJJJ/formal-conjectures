/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD31Long00CompositionalNode090
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e091 : NestedArithmetic.Expr 3 := .scaled (-1) e090
noncomputable def p091 : NestedHorner.Poly 3 := [[[0],[0,0],[0,0]],[[0,0],[0,0,2883],[0,2883]],[[0,0,0],[0,0,0],[0,0]],[[0,25947,43245],[25947,138384,12679],[43245,12679]],[[0,0,0],[0,0,0],[0,0]],[[467046,1610388,333219],[1610388,1033044,16182],[333219,16182]],[[0,0,0],[0,0,0],[0,0]],[[16221060,15098922,1022690],[15098922,3072100,7719],[1022690,7719]],[[0,0,0],[0,0,0],[0,0]],[[167530572,65279428,1640117],[65279428,4799916,1395],[1640117,1395]],[[0,0,0],[0,0,0],[0,0]],[[895759632,164738154,1511498],[164738154,4339256,62],[1511498,62]],[[0,0,0],[0,0],[0]],[[2987132286,268449026,826491],[268449026,2344964],[826491]],[[0,0,0],[0,0],[0]],[[6803834492,297493980,265794],[297493980,751812],[265794]],[[0,0,0],[0,0],[0]],[[11148133696,230289049,47151],[230289049,134788],[47151]],[[0,0,0],[0,0],[0]],[[13563235258,125833929,3813],[125833929,11408],[3813]],[[0,0,0],[0,0],[0]],[[12494527618,48373361,62],[48373361,248],[62]],[[0,0],[0]],[[8812755578,12837720],[12837720]],[[0,0],[0]],[[4780766184,2255839],[2255839]],[[0,0],[0]],[[1991522708,241242],[241242]],[[0,0],[0]],[[631866490,12989],[12989]],[[0,0],[0]],[[150203680,186],[186]],[[0]],[[26003792]],[[0]],[[3124738]],[[0]],[[239072]],[[0]],[[9734]],[[0]],[[124]]]
theorem step091 : p091=NestedHorner.scale (-1) p090 := by decide +kernel
#print axioms step091
theorem h091 : NestedArithmetic.compile e091=p091 := StagedExprCompile.compile_scaled (-1) e091 e090 p090 p091 rfl h090 step091
#print axioms h091
end Gebendorfer.RadenkovicGutman.FixedDegree31Long00Compositional
