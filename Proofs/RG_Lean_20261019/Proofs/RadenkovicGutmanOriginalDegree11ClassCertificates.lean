/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree11Class11
import Proofs.RadenkovicGutmanFixedDegree11Class12
import Proofs.RadenkovicGutmanFixedDegree11Class13
import Proofs.RadenkovicGutmanFixedDegree11Class14
import Proofs.RadenkovicGutmanFixedDegree11Class10
import Proofs.RadenkovicGutmanFixedDegree11Class22
import Proofs.RadenkovicGutmanFixedDegree11Class23
import Proofs.RadenkovicGutmanFixedDegree11Class24
import Proofs.RadenkovicGutmanFixedDegree11Class20
import Proofs.RadenkovicGutmanFixedDegree11Class33
import Proofs.RadenkovicGutmanFixedDegree11Class34
import Proofs.RadenkovicGutmanFixedDegree11Class30
import Proofs.RadenkovicGutmanFixedDegree11Class44
import Proofs.RadenkovicGutmanFixedDegree11Class40
import Proofs.RadenkovicGutmanD11UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree11ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 11 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree11Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree11Class11.reserve]
  · have hb := FixedDegree11Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree11Class12.reserve]
  · have hb := FixedDegree11Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree11Class13.reserve]
  · have hb := FixedDegree11Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree11Class14.reserve]
  · have hb := FixedDegree11Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree11Class10.reserve]
  · omega
  · have hb := FixedDegree11Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree11Class22.reserve]
  · have hb := FixedDegree11Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree11Class23.reserve]
  · have hb := FixedDegree11Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree11Class24.reserve]
  · have hb := FixedDegree11Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree11Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree11Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree11Class33.reserve]
  · have hb := FixedDegree11Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree11Class34.reserve]
  · have hb := FixedDegree11Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree11Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree11Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree11Class44.reserve]
  · have hb := FixedDegree11Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree11Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D11UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D11UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree11ClassCertificates
