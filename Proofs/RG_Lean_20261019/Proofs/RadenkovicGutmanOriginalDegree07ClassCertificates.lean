/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree07Class11
import Proofs.RadenkovicGutmanFixedDegree07Class12
import Proofs.RadenkovicGutmanFixedDegree07Class13
import Proofs.RadenkovicGutmanFixedDegree07Class14
import Proofs.RadenkovicGutmanFixedDegree07Class10
import Proofs.RadenkovicGutmanFixedDegree07Class22
import Proofs.RadenkovicGutmanFixedDegree07Class23
import Proofs.RadenkovicGutmanFixedDegree07Class24
import Proofs.RadenkovicGutmanFixedDegree07Class20
import Proofs.RadenkovicGutmanFixedDegree07Class33
import Proofs.RadenkovicGutmanFixedDegree07Class34
import Proofs.RadenkovicGutmanFixedDegree07Class30
import Proofs.RadenkovicGutmanFixedDegree07Class44
import Proofs.RadenkovicGutmanFixedDegree07Class40
import Proofs.RadenkovicGutmanD7UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree07ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 7 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree07Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree07Class11.reserve]
  · have hb := FixedDegree07Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree07Class12.reserve]
  · have hb := FixedDegree07Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree07Class13.reserve]
  · have hb := FixedDegree07Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree07Class14.reserve]
  · have hb := FixedDegree07Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree07Class10.reserve]
  · omega
  · have hb := FixedDegree07Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree07Class22.reserve]
  · have hb := FixedDegree07Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree07Class23.reserve]
  · have hb := FixedDegree07Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree07Class24.reserve]
  · have hb := FixedDegree07Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree07Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree07Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree07Class33.reserve]
  · have hb := FixedDegree07Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree07Class34.reserve]
  · have hb := FixedDegree07Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree07Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree07Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree07Class44.reserve]
  · have hb := FixedDegree07Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree07Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D7UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D7UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree07ClassCertificates
