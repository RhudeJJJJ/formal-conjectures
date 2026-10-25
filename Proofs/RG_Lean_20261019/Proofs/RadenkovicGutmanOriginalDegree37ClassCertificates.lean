/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree37Class11
import Proofs.RadenkovicGutmanFixedDegree37Class12
import Proofs.RadenkovicGutmanFixedDegree37Class13
import Proofs.RadenkovicGutmanFixedDegree37Class14
import Proofs.RadenkovicGutmanFixedDegree37Class10
import Proofs.RadenkovicGutmanFixedDegree37Class22
import Proofs.RadenkovicGutmanFixedDegree37Class23
import Proofs.RadenkovicGutmanFixedDegree37Class24
import Proofs.RadenkovicGutmanFixedDegree37Class20
import Proofs.RadenkovicGutmanFixedDegree37Class33
import Proofs.RadenkovicGutmanFixedDegree37Class34
import Proofs.RadenkovicGutmanFixedDegree37Class30
import Proofs.RadenkovicGutmanFixedDegree37Class44
import Proofs.RadenkovicGutmanFixedDegree37Class40
import Proofs.RadenkovicGutmanD37UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree37ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 37 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree37Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree37Class11.reserve]
  · have hb := FixedDegree37Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree37Class12.reserve]
  · have hb := FixedDegree37Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree37Class13.reserve]
  · have hb := FixedDegree37Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree37Class14.reserve]
  · have hb := FixedDegree37Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree37Class10.reserve]
  · omega
  · have hb := FixedDegree37Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree37Class22.reserve]
  · have hb := FixedDegree37Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree37Class23.reserve]
  · have hb := FixedDegree37Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree37Class24.reserve]
  · have hb := FixedDegree37Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree37Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree37Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree37Class33.reserve]
  · have hb := FixedDegree37Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree37Class34.reserve]
  · have hb := FixedDegree37Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree37Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree37Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree37Class44.reserve]
  · have hb := FixedDegree37Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree37Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D37UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D37UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree37ClassCertificates
