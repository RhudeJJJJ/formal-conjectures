/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree34Class11
import Proofs.RadenkovicGutmanFixedDegree34Class12
import Proofs.RadenkovicGutmanFixedDegree34Class13
import Proofs.RadenkovicGutmanFixedDegree34Class14
import Proofs.RadenkovicGutmanFixedDegree34Class10
import Proofs.RadenkovicGutmanFixedDegree34Class22
import Proofs.RadenkovicGutmanFixedDegree34Class23
import Proofs.RadenkovicGutmanFixedDegree34Class24
import Proofs.RadenkovicGutmanFixedDegree34Class20
import Proofs.RadenkovicGutmanFixedDegree34Class33
import Proofs.RadenkovicGutmanFixedDegree34Class34
import Proofs.RadenkovicGutmanFixedDegree34Class30
import Proofs.RadenkovicGutmanFixedDegree34Class44
import Proofs.RadenkovicGutmanFixedDegree34Class40
import Proofs.RadenkovicGutmanD34UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree34ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 34 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree34Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree34Class11.reserve]
  · have hb := FixedDegree34Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree34Class12.reserve]
  · have hb := FixedDegree34Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree34Class13.reserve]
  · have hb := FixedDegree34Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree34Class14.reserve]
  · have hb := FixedDegree34Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree34Class10.reserve]
  · omega
  · have hb := FixedDegree34Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree34Class22.reserve]
  · have hb := FixedDegree34Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree34Class23.reserve]
  · have hb := FixedDegree34Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree34Class24.reserve]
  · have hb := FixedDegree34Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree34Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree34Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree34Class33.reserve]
  · have hb := FixedDegree34Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree34Class34.reserve]
  · have hb := FixedDegree34Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree34Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree34Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree34Class44.reserve]
  · have hb := FixedDegree34Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree34Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D34UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D34UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree34ClassCertificates
