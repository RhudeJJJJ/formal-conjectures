/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree09Class11
import Proofs.RadenkovicGutmanFixedDegree09Class12
import Proofs.RadenkovicGutmanFixedDegree09Class13
import Proofs.RadenkovicGutmanFixedDegree09Class14
import Proofs.RadenkovicGutmanFixedDegree09Class10
import Proofs.RadenkovicGutmanFixedDegree09Class22
import Proofs.RadenkovicGutmanFixedDegree09Class23
import Proofs.RadenkovicGutmanFixedDegree09Class24
import Proofs.RadenkovicGutmanFixedDegree09Class20
import Proofs.RadenkovicGutmanFixedDegree09Class33
import Proofs.RadenkovicGutmanFixedDegree09Class34
import Proofs.RadenkovicGutmanFixedDegree09Class30
import Proofs.RadenkovicGutmanFixedDegree09Class44
import Proofs.RadenkovicGutmanFixedDegree09Class40
import Proofs.RadenkovicGutmanD9UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree09ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 9 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree09Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree09Class11.reserve]
  · have hb := FixedDegree09Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree09Class12.reserve]
  · have hb := FixedDegree09Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree09Class13.reserve]
  · have hb := FixedDegree09Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree09Class14.reserve]
  · have hb := FixedDegree09Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree09Class10.reserve]
  · omega
  · have hb := FixedDegree09Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree09Class22.reserve]
  · have hb := FixedDegree09Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree09Class23.reserve]
  · have hb := FixedDegree09Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree09Class24.reserve]
  · have hb := FixedDegree09Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree09Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree09Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree09Class33.reserve]
  · have hb := FixedDegree09Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree09Class34.reserve]
  · have hb := FixedDegree09Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree09Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree09Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree09Class44.reserve]
  · have hb := FixedDegree09Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree09Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D9UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D9UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree09ClassCertificates
