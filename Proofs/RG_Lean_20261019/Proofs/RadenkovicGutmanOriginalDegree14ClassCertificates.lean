/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree14Class11
import Proofs.RadenkovicGutmanFixedDegree14Class12
import Proofs.RadenkovicGutmanFixedDegree14Class13
import Proofs.RadenkovicGutmanFixedDegree14Class14
import Proofs.RadenkovicGutmanFixedDegree14Class10
import Proofs.RadenkovicGutmanFixedDegree14Class22
import Proofs.RadenkovicGutmanFixedDegree14Class23
import Proofs.RadenkovicGutmanFixedDegree14Class24
import Proofs.RadenkovicGutmanFixedDegree14Class20
import Proofs.RadenkovicGutmanFixedDegree14Class33
import Proofs.RadenkovicGutmanFixedDegree14Class34
import Proofs.RadenkovicGutmanFixedDegree14Class30
import Proofs.RadenkovicGutmanFixedDegree14Class44
import Proofs.RadenkovicGutmanFixedDegree14Class40
import Proofs.RadenkovicGutmanD14UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree14ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 14 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree14Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree14Class11.reserve]
  · have hb := FixedDegree14Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree14Class12.reserve]
  · have hb := FixedDegree14Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree14Class13.reserve]
  · have hb := FixedDegree14Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree14Class14.reserve]
  · have hb := FixedDegree14Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree14Class10.reserve]
  · omega
  · have hb := FixedDegree14Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree14Class22.reserve]
  · have hb := FixedDegree14Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree14Class23.reserve]
  · have hb := FixedDegree14Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree14Class24.reserve]
  · have hb := FixedDegree14Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree14Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree14Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree14Class33.reserve]
  · have hb := FixedDegree14Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree14Class34.reserve]
  · have hb := FixedDegree14Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree14Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree14Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree14Class44.reserve]
  · have hb := FixedDegree14Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree14Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D14UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D14UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree14ClassCertificates
