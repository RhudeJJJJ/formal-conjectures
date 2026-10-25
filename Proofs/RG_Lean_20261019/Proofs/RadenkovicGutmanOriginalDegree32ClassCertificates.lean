/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree32Class11
import Proofs.RadenkovicGutmanFixedDegree32Class12
import Proofs.RadenkovicGutmanFixedDegree32Class13
import Proofs.RadenkovicGutmanFixedDegree32Class14
import Proofs.RadenkovicGutmanFixedDegree32Class10
import Proofs.RadenkovicGutmanFixedDegree32Class22
import Proofs.RadenkovicGutmanFixedDegree32Class23
import Proofs.RadenkovicGutmanFixedDegree32Class24
import Proofs.RadenkovicGutmanFixedDegree32Class20
import Proofs.RadenkovicGutmanFixedDegree32Class33
import Proofs.RadenkovicGutmanFixedDegree32Class34
import Proofs.RadenkovicGutmanFixedDegree32Class30
import Proofs.RadenkovicGutmanFixedDegree32Class44
import Proofs.RadenkovicGutmanFixedDegree32Class40
import Proofs.RadenkovicGutmanD32UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree32ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 32 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree32Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree32Class11.reserve]
  · have hb := FixedDegree32Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree32Class12.reserve]
  · have hb := FixedDegree32Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree32Class13.reserve]
  · have hb := FixedDegree32Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree32Class14.reserve]
  · have hb := FixedDegree32Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree32Class10.reserve]
  · omega
  · have hb := FixedDegree32Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree32Class22.reserve]
  · have hb := FixedDegree32Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree32Class23.reserve]
  · have hb := FixedDegree32Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree32Class24.reserve]
  · have hb := FixedDegree32Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree32Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree32Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree32Class33.reserve]
  · have hb := FixedDegree32Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree32Class34.reserve]
  · have hb := FixedDegree32Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree32Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree32Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree32Class44.reserve]
  · have hb := FixedDegree32Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree32Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D32UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D32UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree32ClassCertificates
