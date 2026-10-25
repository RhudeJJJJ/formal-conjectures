/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree42Class11
import Proofs.RadenkovicGutmanFixedDegree42Class12
import Proofs.RadenkovicGutmanFixedDegree42Class13
import Proofs.RadenkovicGutmanFixedDegree42Class14
import Proofs.RadenkovicGutmanFixedDegree42Class10
import Proofs.RadenkovicGutmanFixedDegree42Class22
import Proofs.RadenkovicGutmanFixedDegree42Class23
import Proofs.RadenkovicGutmanFixedDegree42Class24
import Proofs.RadenkovicGutmanFixedDegree42Class20
import Proofs.RadenkovicGutmanFixedDegree42Class33
import Proofs.RadenkovicGutmanFixedDegree42Class34
import Proofs.RadenkovicGutmanFixedDegree42Class30
import Proofs.RadenkovicGutmanFixedDegree42Class44
import Proofs.RadenkovicGutmanFixedDegree42Class40
import Proofs.RadenkovicGutmanD42UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree42ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 42 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree42Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree42Class11.reserve]
  · have hb := FixedDegree42Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree42Class12.reserve]
  · have hb := FixedDegree42Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree42Class13.reserve]
  · have hb := FixedDegree42Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree42Class14.reserve]
  · have hb := FixedDegree42Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree42Class10.reserve]
  · omega
  · have hb := FixedDegree42Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree42Class22.reserve]
  · have hb := FixedDegree42Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree42Class23.reserve]
  · have hb := FixedDegree42Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree42Class24.reserve]
  · have hb := FixedDegree42Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree42Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree42Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree42Class33.reserve]
  · have hb := FixedDegree42Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree42Class34.reserve]
  · have hb := FixedDegree42Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree42Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree42Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree42Class44.reserve]
  · have hb := FixedDegree42Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree42Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D42UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D42UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree42ClassCertificates
