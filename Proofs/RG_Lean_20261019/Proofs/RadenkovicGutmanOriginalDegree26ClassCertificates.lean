/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree26Class11
import Proofs.RadenkovicGutmanFixedDegree26Class12
import Proofs.RadenkovicGutmanFixedDegree26Class13
import Proofs.RadenkovicGutmanFixedDegree26Class14
import Proofs.RadenkovicGutmanFixedDegree26Class10
import Proofs.RadenkovicGutmanFixedDegree26Class22
import Proofs.RadenkovicGutmanFixedDegree26Class23
import Proofs.RadenkovicGutmanFixedDegree26Class24
import Proofs.RadenkovicGutmanFixedDegree26Class20
import Proofs.RadenkovicGutmanFixedDegree26Class33
import Proofs.RadenkovicGutmanFixedDegree26Class34
import Proofs.RadenkovicGutmanFixedDegree26Class30
import Proofs.RadenkovicGutmanFixedDegree26Class44
import Proofs.RadenkovicGutmanFixedDegree26Class40
import Proofs.RadenkovicGutmanD26UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree26ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 26 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree26Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree26Class11.reserve]
  · have hb := FixedDegree26Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree26Class12.reserve]
  · have hb := FixedDegree26Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree26Class13.reserve]
  · have hb := FixedDegree26Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree26Class14.reserve]
  · have hb := FixedDegree26Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree26Class10.reserve]
  · omega
  · have hb := FixedDegree26Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree26Class22.reserve]
  · have hb := FixedDegree26Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree26Class23.reserve]
  · have hb := FixedDegree26Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree26Class24.reserve]
  · have hb := FixedDegree26Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree26Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree26Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree26Class33.reserve]
  · have hb := FixedDegree26Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree26Class34.reserve]
  · have hb := FixedDegree26Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree26Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree26Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree26Class44.reserve]
  · have hb := FixedDegree26Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree26Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D26UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D26UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree26ClassCertificates
