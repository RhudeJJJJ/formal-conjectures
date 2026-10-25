/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD44Long00CompositionalNode076
import Proofs.RadenkovicGutmanStagedExprCompile
namespace Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
noncomputable def e077 : NestedArithmetic.Expr 3 := .scaled (-1) e076
noncomputable def p077 : NestedHorner.Poly 3 := [[[0],[0],[0]],[[0,0],[0,0],[0]],[[0,0,17424],[0,34848],[17424]],[[0,0,0],[0,0],[0]],[[0,574992,151008],[574992,302016],[151008]],[[0,0,0],[0,0],[0]],[[4704480,6429456,513040],[6429456,1026080],[513040]],[[0,0,0],[0,0],[0]],[[64294560,30718512,886688],[30718512,1773376],[886688]],[[0,0,0],[0,0],[0]],[[391935456,83151200,859584],[83151200,1719168],[859584]],[[0,0,0],[0,0],[0]],[[1418731776,142727728,484000],[142727728,968000],[484000]],[[0,0,0],[0,0],[0]],[[3424001856,164438032,156816],[164438032,313632],[156816]],[[0,0,0],[0,0],[0]],[[5858560576,130943296,27104],[130943296,54208],[27104]],[[0,0,0],[0,0],[0]],[[7369202016,72907824,1936],[72907824,3872],[1936]],[[0,0],[0]],[[6965646688,28283024],[28283024]],[[0,0],[0]],[[5009841408,7484576],[7484576]],[[0,0],[0]],[[2755659808,1287440],[1287440]],[[0,0],[0]],[[1157375648,129712],[129712]],[[0,0],[0]],[[367894208,5808],[5808]],[[0]],[[86910912]],[[0]],[[14775552]],[[0]],[[1707552]],[[0]],[[120032]],[[0]],[[3872]]]
theorem step077 : p077=NestedHorner.scale (-1) p076 := by decide +kernel
#print axioms step077
theorem h077 : NestedArithmetic.compile e077=p077 := StagedExprCompile.compile_scaled (-1) e077 e076 p076 p077 rfl h076 step077
#print axioms h077
end Gebendorfer.RadenkovicGutman.FixedDegree44Long00Compositional
