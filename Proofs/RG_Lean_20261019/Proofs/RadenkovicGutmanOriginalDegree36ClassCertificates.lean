/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree36Class11
import Proofs.RadenkovicGutmanFixedDegree36Class12
import Proofs.RadenkovicGutmanFixedDegree36Class13
import Proofs.RadenkovicGutmanFixedDegree36Class14
import Proofs.RadenkovicGutmanFixedDegree36Class10
import Proofs.RadenkovicGutmanFixedDegree36Class22
import Proofs.RadenkovicGutmanFixedDegree36Class23
import Proofs.RadenkovicGutmanFixedDegree36Class24
import Proofs.RadenkovicGutmanFixedDegree36Class20
import Proofs.RadenkovicGutmanFixedDegree36Class33
import Proofs.RadenkovicGutmanFixedDegree36Class34
import Proofs.RadenkovicGutmanFixedDegree36Class30
import Proofs.RadenkovicGutmanFixedDegree36Class44
import Proofs.RadenkovicGutmanFixedDegree36Class40
import Proofs.RadenkovicGutmanD36UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree36ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 36 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree36Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree36Class11.reserve]
  · have hb := FixedDegree36Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree36Class12.reserve]
  · have hb := FixedDegree36Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree36Class13.reserve]
  · have hb := FixedDegree36Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree36Class14.reserve]
  · have hb := FixedDegree36Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree36Class10.reserve]
  · omega
  · have hb := FixedDegree36Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree36Class22.reserve]
  · have hb := FixedDegree36Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree36Class23.reserve]
  · have hb := FixedDegree36Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree36Class24.reserve]
  · have hb := FixedDegree36Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree36Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree36Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree36Class33.reserve]
  · have hb := FixedDegree36Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree36Class34.reserve]
  · have hb := FixedDegree36Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree36Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree36Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree36Class44.reserve]
  · have hb := FixedDegree36Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree36Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D36UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D36UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree36ClassCertificates
