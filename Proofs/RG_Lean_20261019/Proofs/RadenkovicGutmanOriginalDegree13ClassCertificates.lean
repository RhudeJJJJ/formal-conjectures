/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree13Class11
import Proofs.RadenkovicGutmanFixedDegree13Class12
import Proofs.RadenkovicGutmanFixedDegree13Class13
import Proofs.RadenkovicGutmanFixedDegree13Class14
import Proofs.RadenkovicGutmanFixedDegree13Class10
import Proofs.RadenkovicGutmanFixedDegree13Class22
import Proofs.RadenkovicGutmanFixedDegree13Class23
import Proofs.RadenkovicGutmanFixedDegree13Class24
import Proofs.RadenkovicGutmanFixedDegree13Class20
import Proofs.RadenkovicGutmanFixedDegree13Class33
import Proofs.RadenkovicGutmanFixedDegree13Class34
import Proofs.RadenkovicGutmanFixedDegree13Class30
import Proofs.RadenkovicGutmanFixedDegree13Class44
import Proofs.RadenkovicGutmanFixedDegree13Class40
import Proofs.RadenkovicGutmanD13UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree13ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 13 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree13Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree13Class11.reserve]
  · have hb := FixedDegree13Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree13Class12.reserve]
  · have hb := FixedDegree13Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree13Class13.reserve]
  · have hb := FixedDegree13Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree13Class14.reserve]
  · have hb := FixedDegree13Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree13Class10.reserve]
  · omega
  · have hb := FixedDegree13Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree13Class22.reserve]
  · have hb := FixedDegree13Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree13Class23.reserve]
  · have hb := FixedDegree13Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree13Class24.reserve]
  · have hb := FixedDegree13Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree13Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree13Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree13Class33.reserve]
  · have hb := FixedDegree13Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree13Class34.reserve]
  · have hb := FixedDegree13Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree13Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree13Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree13Class44.reserve]
  · have hb := FixedDegree13Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree13Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D13UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D13UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree13ClassCertificates
