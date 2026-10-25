/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree16Class11
import Proofs.RadenkovicGutmanFixedDegree16Class12
import Proofs.RadenkovicGutmanFixedDegree16Class13
import Proofs.RadenkovicGutmanFixedDegree16Class14
import Proofs.RadenkovicGutmanFixedDegree16Class10
import Proofs.RadenkovicGutmanFixedDegree16Class22
import Proofs.RadenkovicGutmanFixedDegree16Class23
import Proofs.RadenkovicGutmanFixedDegree16Class24
import Proofs.RadenkovicGutmanFixedDegree16Class20
import Proofs.RadenkovicGutmanFixedDegree16Class33
import Proofs.RadenkovicGutmanFixedDegree16Class34
import Proofs.RadenkovicGutmanFixedDegree16Class30
import Proofs.RadenkovicGutmanFixedDegree16Class44
import Proofs.RadenkovicGutmanFixedDegree16Class40
import Proofs.RadenkovicGutmanD16UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree16ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 16 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree16Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree16Class11.reserve]
  · have hb := FixedDegree16Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree16Class12.reserve]
  · have hb := FixedDegree16Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree16Class13.reserve]
  · have hb := FixedDegree16Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree16Class14.reserve]
  · have hb := FixedDegree16Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree16Class10.reserve]
  · omega
  · have hb := FixedDegree16Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree16Class22.reserve]
  · have hb := FixedDegree16Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree16Class23.reserve]
  · have hb := FixedDegree16Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree16Class24.reserve]
  · have hb := FixedDegree16Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree16Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree16Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree16Class33.reserve]
  · have hb := FixedDegree16Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree16Class34.reserve]
  · have hb := FixedDegree16Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree16Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree16Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree16Class44.reserve]
  · have hb := FixedDegree16Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree16Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D16UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D16UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree16ClassCertificates
