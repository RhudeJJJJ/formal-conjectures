/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanGeneralPathPolynomialPayments

namespace Gebendorfer.RadenkovicGutman.Mean16PolynomialBase
open CoreQuotient PolynomialPathMap RationalComplexPolynomial
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def as : List ℚ := [(49/64),(7/4),1]

def bs : List ℚ := [(-49/64),(-1785/256),(-237/32),(5/4),2]

def cs : List ℚ := [(-71/64),(3/4),1]

def es : List ℚ := [(71/64),(-569/256),(-173/32),(5/4),2]

def us : List ℚ := [0,0,(200930625/4194304),0,(2721395507041/4294967296),0,(81950816371/33554432),0,(4104214991/1048576),0,(12195957/4096),0,(294127/256),0,(435/2),0,16]

def vs : List ℚ := [0,0,(200930625/4194304),0,(2091825/16384),0,(56547/512),0,(145/4),0,4]

def js : List ℚ := [0,0,0,0,(5487966854881/4294967296),0,(163654557619/33554432),0,(7218235599/1048576),0,(18601141/4096),0,(388719/256),0,(499/2),0,16]

def ns : List ℚ := [0,0,(2342641/65536),0,(69859/1024),0,(499/16),0,4]

def sep : List ℚ := [0,0,(927601/65536),0,(39139/1024),0,(371/16),0,4]

theorem path_checked : GeneralPathPolynomials.accepts (15/8) 0 0 as bs cs es=true := by
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
end Gebendorfer.RadenkovicGutman.Mean16PolynomialBase
