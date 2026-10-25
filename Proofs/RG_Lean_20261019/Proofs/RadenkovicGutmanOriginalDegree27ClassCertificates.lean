/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree27Class11
import Proofs.RadenkovicGutmanFixedDegree27Class12
import Proofs.RadenkovicGutmanFixedDegree27Class13
import Proofs.RadenkovicGutmanFixedDegree27Class14
import Proofs.RadenkovicGutmanFixedDegree27Class10
import Proofs.RadenkovicGutmanFixedDegree27Class22
import Proofs.RadenkovicGutmanFixedDegree27Class23
import Proofs.RadenkovicGutmanFixedDegree27Class24
import Proofs.RadenkovicGutmanFixedDegree27Class20
import Proofs.RadenkovicGutmanFixedDegree27Class33
import Proofs.RadenkovicGutmanFixedDegree27Class34
import Proofs.RadenkovicGutmanFixedDegree27Class30
import Proofs.RadenkovicGutmanFixedDegree27Class44
import Proofs.RadenkovicGutmanFixedDegree27Class40
import Proofs.RadenkovicGutmanD27UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree27ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 27 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree27Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree27Class11.reserve]
  · have hb := FixedDegree27Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree27Class12.reserve]
  · have hb := FixedDegree27Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree27Class13.reserve]
  · have hb := FixedDegree27Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree27Class14.reserve]
  · have hb := FixedDegree27Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree27Class10.reserve]
  · omega
  · have hb := FixedDegree27Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree27Class22.reserve]
  · have hb := FixedDegree27Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree27Class23.reserve]
  · have hb := FixedDegree27Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree27Class24.reserve]
  · have hb := FixedDegree27Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree27Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree27Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree27Class33.reserve]
  · have hb := FixedDegree27Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree27Class34.reserve]
  · have hb := FixedDegree27Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree27Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree27Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree27Class44.reserve]
  · have hb := FixedDegree27Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree27Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D27UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D27UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree27ClassCertificates
