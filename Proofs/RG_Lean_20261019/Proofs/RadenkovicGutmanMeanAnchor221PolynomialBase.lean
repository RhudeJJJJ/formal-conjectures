/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanGeneralPathPolynomialPayments

namespace Gebendorfer.RadenkovicGutman.MeanAnchor221PolynomialBase
open CoreQuotient PolynomialPathMap RationalComplexPolynomial
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def as : List ℚ := [(441/529),(42/23),1]

def bs : List ℚ := [(-441/529),(-88704/12167),(-3863/529),(34/23),2]

def cs : List ℚ := [(-571/529),(19/23),1]

def es : List ℚ := [(571/529),(-29985/12167),(-2805/529),(34/23),2]

def us : List ℚ := [0,0,(4132275840000/78310985281),0,(15643229319142170496/21914624432020321),0,(110779547988758436/41426511213649),0,(324940915424904/78310985281),0,(456838009828/148035889),0,(327848784/279841),0,(115936/529),0,16]

def vs : List ℚ := [0,0,(4132275840000/78310985281),0,(20250761344/148035889),0,(32605092/279841),0,(19752/529),0,4]

def js : List ℚ := [0,0,0,0,(33862961083256121600/21914624432020321),0,(229760716792763520/41426511213649),0,(583022690975376/78310985281),0,(702291959424/148035889),0,(433758816/279841),0,(132864/529),0,16]

def ns : List ℚ := [0,0,(5819189040/148035889),0,(19741644/279841),0,(16608/529),0,4]

def sep : List ℚ := [0,0,(2173050192/148035889),0,(10835400/279841),0,(12376/529),0,4]

theorem path_checked : GeneralPathPolynomials.accepts (44/23) 0 0 as bs cs es=true := by
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
end Gebendorfer.RadenkovicGutman.MeanAnchor221PolynomialBase
