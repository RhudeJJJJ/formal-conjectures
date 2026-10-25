/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree19Class11
import Proofs.RadenkovicGutmanFixedDegree19Class12
import Proofs.RadenkovicGutmanFixedDegree19Class13
import Proofs.RadenkovicGutmanFixedDegree19Class14
import Proofs.RadenkovicGutmanFixedDegree19Class10
import Proofs.RadenkovicGutmanFixedDegree19Class22
import Proofs.RadenkovicGutmanFixedDegree19Class23
import Proofs.RadenkovicGutmanFixedDegree19Class24
import Proofs.RadenkovicGutmanFixedDegree19Class20
import Proofs.RadenkovicGutmanFixedDegree19Class33
import Proofs.RadenkovicGutmanFixedDegree19Class34
import Proofs.RadenkovicGutmanFixedDegree19Class30
import Proofs.RadenkovicGutmanFixedDegree19Class44
import Proofs.RadenkovicGutmanFixedDegree19Class40
import Proofs.RadenkovicGutmanD19UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree19ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 19 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree19Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree19Class11.reserve]
  · have hb := FixedDegree19Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree19Class12.reserve]
  · have hb := FixedDegree19Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree19Class13.reserve]
  · have hb := FixedDegree19Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree19Class14.reserve]
  · have hb := FixedDegree19Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree19Class10.reserve]
  · omega
  · have hb := FixedDegree19Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree19Class22.reserve]
  · have hb := FixedDegree19Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree19Class23.reserve]
  · have hb := FixedDegree19Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree19Class24.reserve]
  · have hb := FixedDegree19Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree19Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree19Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree19Class33.reserve]
  · have hb := FixedDegree19Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree19Class34.reserve]
  · have hb := FixedDegree19Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree19Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree19Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree19Class44.reserve]
  · have hb := FixedDegree19Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree19Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D19UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D19UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree19ClassCertificates
