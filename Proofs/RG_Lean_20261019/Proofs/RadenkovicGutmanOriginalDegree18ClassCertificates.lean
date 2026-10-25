/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree18Class11
import Proofs.RadenkovicGutmanFixedDegree18Class12
import Proofs.RadenkovicGutmanFixedDegree18Class13
import Proofs.RadenkovicGutmanFixedDegree18Class14
import Proofs.RadenkovicGutmanFixedDegree18Class10
import Proofs.RadenkovicGutmanFixedDegree18Class22
import Proofs.RadenkovicGutmanFixedDegree18Class23
import Proofs.RadenkovicGutmanFixedDegree18Class24
import Proofs.RadenkovicGutmanFixedDegree18Class20
import Proofs.RadenkovicGutmanFixedDegree18Class33
import Proofs.RadenkovicGutmanFixedDegree18Class34
import Proofs.RadenkovicGutmanFixedDegree18Class30
import Proofs.RadenkovicGutmanFixedDegree18Class44
import Proofs.RadenkovicGutmanFixedDegree18Class40
import Proofs.RadenkovicGutmanD18UpperCompositionalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree18ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 18 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree18Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree18Class11.reserve]
  · have hb := FixedDegree18Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree18Class12.reserve]
  · have hb := FixedDegree18Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree18Class13.reserve]
  · have hb := FixedDegree18Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree18Class14.reserve]
  · have hb := FixedDegree18Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree18Class10.reserve]
  · omega
  · have hb := FixedDegree18Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree18Class22.reserve]
  · have hb := FixedDegree18Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree18Class23.reserve]
  · have hb := FixedDegree18Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree18Class24.reserve]
  · have hb := FixedDegree18Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree18Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree18Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree18Class33.reserve]
  · have hb := FixedDegree18Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree18Class34.reserve]
  · have hb := FixedDegree18Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree18Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree18Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree18Class44.reserve]
  · have hb := FixedDegree18Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree18Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D18UpperCompositionalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D18UpperCompositionalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree18ClassCertificates
