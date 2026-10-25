/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree20Class11
import Proofs.RadenkovicGutmanFixedDegree20Class12
import Proofs.RadenkovicGutmanFixedDegree20Class13
import Proofs.RadenkovicGutmanFixedDegree20Class14
import Proofs.RadenkovicGutmanFixedDegree20Class10
import Proofs.RadenkovicGutmanFixedDegree20Class22
import Proofs.RadenkovicGutmanFixedDegree20Class23
import Proofs.RadenkovicGutmanFixedDegree20Class24
import Proofs.RadenkovicGutmanFixedDegree20Class20
import Proofs.RadenkovicGutmanFixedDegree20Class33
import Proofs.RadenkovicGutmanFixedDegree20Class34
import Proofs.RadenkovicGutmanFixedDegree20Class30
import Proofs.RadenkovicGutmanFixedDegree20Class44
import Proofs.RadenkovicGutmanFixedDegree20Class40
import Proofs.RadenkovicGutmanD20UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree20ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 20 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree20Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree20Class11.reserve]
  · have hb := FixedDegree20Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree20Class12.reserve]
  · have hb := FixedDegree20Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree20Class13.reserve]
  · have hb := FixedDegree20Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree20Class14.reserve]
  · have hb := FixedDegree20Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree20Class10.reserve]
  · omega
  · have hb := FixedDegree20Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree20Class22.reserve]
  · have hb := FixedDegree20Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree20Class23.reserve]
  · have hb := FixedDegree20Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree20Class24.reserve]
  · have hb := FixedDegree20Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree20Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree20Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree20Class33.reserve]
  · have hb := FixedDegree20Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree20Class34.reserve]
  · have hb := FixedDegree20Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree20Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree20Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree20Class44.reserve]
  · have hb := FixedDegree20Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree20Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D20UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D20UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree20ClassCertificates
