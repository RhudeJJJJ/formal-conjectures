/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree38Class11
import Proofs.RadenkovicGutmanFixedDegree38Class12
import Proofs.RadenkovicGutmanFixedDegree38Class13
import Proofs.RadenkovicGutmanFixedDegree38Class14
import Proofs.RadenkovicGutmanFixedDegree38Class10
import Proofs.RadenkovicGutmanFixedDegree38Class22
import Proofs.RadenkovicGutmanFixedDegree38Class23
import Proofs.RadenkovicGutmanFixedDegree38Class24
import Proofs.RadenkovicGutmanFixedDegree38Class20
import Proofs.RadenkovicGutmanFixedDegree38Class33
import Proofs.RadenkovicGutmanFixedDegree38Class34
import Proofs.RadenkovicGutmanFixedDegree38Class30
import Proofs.RadenkovicGutmanFixedDegree38Class44
import Proofs.RadenkovicGutmanFixedDegree38Class40
import Proofs.RadenkovicGutmanD38UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree38ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 38 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree38Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree38Class11.reserve]
  · have hb := FixedDegree38Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree38Class12.reserve]
  · have hb := FixedDegree38Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree38Class13.reserve]
  · have hb := FixedDegree38Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree38Class14.reserve]
  · have hb := FixedDegree38Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree38Class10.reserve]
  · omega
  · have hb := FixedDegree38Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree38Class22.reserve]
  · have hb := FixedDegree38Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree38Class23.reserve]
  · have hb := FixedDegree38Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree38Class24.reserve]
  · have hb := FixedDegree38Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree38Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree38Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree38Class33.reserve]
  · have hb := FixedDegree38Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree38Class34.reserve]
  · have hb := FixedDegree38Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree38Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree38Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree38Class44.reserve]
  · have hb := FixedDegree38Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree38Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D38UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D38UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree38ClassCertificates
