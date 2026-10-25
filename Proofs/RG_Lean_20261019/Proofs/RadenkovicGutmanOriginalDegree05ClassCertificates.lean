/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree05Class11
import Proofs.RadenkovicGutmanFixedDegree05Class12
import Proofs.RadenkovicGutmanFixedDegree05Class13
import Proofs.RadenkovicGutmanFixedDegree05Class14
import Proofs.RadenkovicGutmanFixedDegree05Class10
import Proofs.RadenkovicGutmanFixedDegree05Class22
import Proofs.RadenkovicGutmanFixedDegree05Class23
import Proofs.RadenkovicGutmanFixedDegree05Class24
import Proofs.RadenkovicGutmanFixedDegree05Class20
import Proofs.RadenkovicGutmanFixedDegree05Class33
import Proofs.RadenkovicGutmanFixedDegree05Class34
import Proofs.RadenkovicGutmanFixedDegree05Class30
import Proofs.RadenkovicGutmanFixedDegree05Class44
import Proofs.RadenkovicGutmanFixedDegree05Class40
import Proofs.RadenkovicGutmanD5UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree05ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 5 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree05Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree05Class11.reserve]
  · have hb := FixedDegree05Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree05Class12.reserve]
  · have hb := FixedDegree05Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree05Class13.reserve]
  · have hb := FixedDegree05Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree05Class14.reserve]
  · have hb := FixedDegree05Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree05Class10.reserve]
  · omega
  · have hb := FixedDegree05Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree05Class22.reserve]
  · have hb := FixedDegree05Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree05Class23.reserve]
  · have hb := FixedDegree05Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree05Class24.reserve]
  · have hb := FixedDegree05Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree05Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree05Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree05Class33.reserve]
  · have hb := FixedDegree05Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree05Class34.reserve]
  · have hb := FixedDegree05Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree05Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree05Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree05Class44.reserve]
  · have hb := FixedDegree05Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree05Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D5UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D5UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree05ClassCertificates
