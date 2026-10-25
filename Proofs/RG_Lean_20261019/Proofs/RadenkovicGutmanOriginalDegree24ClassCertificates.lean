/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree24Class11
import Proofs.RadenkovicGutmanFixedDegree24Class12
import Proofs.RadenkovicGutmanFixedDegree24Class13
import Proofs.RadenkovicGutmanFixedDegree24Class14
import Proofs.RadenkovicGutmanFixedDegree24Class10
import Proofs.RadenkovicGutmanFixedDegree24Class22
import Proofs.RadenkovicGutmanFixedDegree24Class23
import Proofs.RadenkovicGutmanFixedDegree24Class24
import Proofs.RadenkovicGutmanFixedDegree24Class20
import Proofs.RadenkovicGutmanFixedDegree24Class33
import Proofs.RadenkovicGutmanFixedDegree24Class34
import Proofs.RadenkovicGutmanFixedDegree24Class30
import Proofs.RadenkovicGutmanFixedDegree24Class44
import Proofs.RadenkovicGutmanFixedDegree24Class40
import Proofs.RadenkovicGutmanD24UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree24ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 24 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree24Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree24Class11.reserve]
  · have hb := FixedDegree24Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree24Class12.reserve]
  · have hb := FixedDegree24Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree24Class13.reserve]
  · have hb := FixedDegree24Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree24Class14.reserve]
  · have hb := FixedDegree24Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree24Class10.reserve]
  · omega
  · have hb := FixedDegree24Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree24Class22.reserve]
  · have hb := FixedDegree24Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree24Class23.reserve]
  · have hb := FixedDegree24Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree24Class24.reserve]
  · have hb := FixedDegree24Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree24Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree24Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree24Class33.reserve]
  · have hb := FixedDegree24Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree24Class34.reserve]
  · have hb := FixedDegree24Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree24Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree24Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree24Class44.reserve]
  · have hb := FixedDegree24Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree24Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D24UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D24UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree24ClassCertificates
