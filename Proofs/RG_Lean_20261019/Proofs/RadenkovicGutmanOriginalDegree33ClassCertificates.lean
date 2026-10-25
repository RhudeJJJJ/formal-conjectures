/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree33Class11
import Proofs.RadenkovicGutmanFixedDegree33Class12
import Proofs.RadenkovicGutmanFixedDegree33Class13
import Proofs.RadenkovicGutmanFixedDegree33Class14
import Proofs.RadenkovicGutmanFixedDegree33Class10
import Proofs.RadenkovicGutmanFixedDegree33Class22
import Proofs.RadenkovicGutmanFixedDegree33Class23
import Proofs.RadenkovicGutmanFixedDegree33Class24
import Proofs.RadenkovicGutmanFixedDegree33Class20
import Proofs.RadenkovicGutmanFixedDegree33Class33
import Proofs.RadenkovicGutmanFixedDegree33Class34
import Proofs.RadenkovicGutmanFixedDegree33Class30
import Proofs.RadenkovicGutmanFixedDegree33Class44
import Proofs.RadenkovicGutmanFixedDegree33Class40
import Proofs.RadenkovicGutmanD33UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree33ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 33 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree33Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree33Class11.reserve]
  · have hb := FixedDegree33Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree33Class12.reserve]
  · have hb := FixedDegree33Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree33Class13.reserve]
  · have hb := FixedDegree33Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree33Class14.reserve]
  · have hb := FixedDegree33Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree33Class10.reserve]
  · omega
  · have hb := FixedDegree33Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree33Class22.reserve]
  · have hb := FixedDegree33Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree33Class23.reserve]
  · have hb := FixedDegree33Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree33Class24.reserve]
  · have hb := FixedDegree33Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree33Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree33Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree33Class33.reserve]
  · have hb := FixedDegree33Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree33Class34.reserve]
  · have hb := FixedDegree33Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree33Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree33Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree33Class44.reserve]
  · have hb := FixedDegree33Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree33Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D33UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D33UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree33ClassCertificates
