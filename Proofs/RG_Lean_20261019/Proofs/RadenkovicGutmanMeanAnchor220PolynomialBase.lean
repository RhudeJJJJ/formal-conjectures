/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanGeneralPathPolynomialPayments

namespace Gebendorfer.RadenkovicGutman.MeanAnchor220PolynomialBase
open CoreQuotient PolynomialPathMap RationalComplexPolynomial
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def as : List ℚ := [(625/676),(25/13),1]

def bs : List ℚ := [(-625/676),(-67575/8788),(-2415/338),(23/13),2]

def cs : List ℚ := [(-701/676),(12/13),1]

def es : List ℚ := [(701/676),(-24311/8788),(-1739/338),(23/13),2]

def us : List ℚ := [0,0,(3082394705625/52206766144),0,(4937328583020756001/5964309791355136),0,(13208242259591707/4411471739168),0,(58350577825295/13051691536),0,(15617668305/4826809),0,(34379503/28561),0,(37464/169),0,16]

def vs : List ℚ := [0,0,(3082394705625/52206766144),0,(2882560851/19307236),0,(7132167/57122),0,(6556/169),0,4]

def js : List ℚ := [0,0,0,0,(11582029735453515625/5964309791355136),0,(28600578379069375/4411471739168),0,(107101962476511/13051691536),0,(24219952177/4826809),0,(45526743/28561),0,(42872/169),0,16]

def ns : List ℚ := [0,0,(3403238125/77228944),0,(8403931/114244),0,(5359/169),0,4]

def sep : List ℚ := [0,0,(1189120453/77228944),0,(4502059/114244),0,(4007/169),0,4]

theorem path_checked : GeneralPathPolynomials.accepts (51/26) 0 0 as bs cs es=true := by
  rw [GeneralPathPolynomials.accepts,decide_eq_true_eq]
  refine ⟨?_,?_,?_,?_⟩
  all_goals apply Polynomial.funext
  all_goals intro t
  all_goals norm_num [as,bs,cs,es,ofList,GeneralPathPolynomials.sourceSlope,
    GeneralPathPolynomials.sourceCenter,GeneralPathPolynomials.sourceOffset,
    GeneralPathPolynomials.fusedSlope,GeneralPathPolynomials.fusedCenter,
    GeneralPathPolynomials.fusedOffset,GeneralPathPolynomials.centerPoly,
    GeneralPathPolynomials.scalePoly,numPoly,denPoly,pointPoly,
    PathRecurrence.num,PathRecurrence.den,PathRecurrence.state]
  all_goals ring
theorem norms_checked : RationalMobiusPolynomials.accepts as bs cs es us vs js ns sep=true := by
  rw [RationalMobiusPolynomials.accepts,decide_eq_true_eq]
  refine ⟨?_,?_,?_,?_,?_⟩
  all_goals apply Polynomial.funext
  all_goals intro t
  all_goals norm_num [as,bs,cs,es,us,vs,js,ns,sep,ofList,parts,normPolynomial,
    RationalMobiusPolynomials.U,RationalMobiusPolynomials.V,RationalMobiusPolynomials.J,
    RationalMobiusPolynomials.N,RationalMobiusPolynomials.E]
  all_goals ring

#print axioms path_checked
#print axioms norms_checked
end Gebendorfer.RadenkovicGutman.MeanAnchor220PolynomialBase
