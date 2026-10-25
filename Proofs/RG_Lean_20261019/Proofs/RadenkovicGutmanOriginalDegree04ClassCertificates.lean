/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeFourToFortyfiveDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree04Class11
import Proofs.RadenkovicGutmanFixedDegree04Class12
import Proofs.RadenkovicGutmanFixedDegree04Class13
import Proofs.RadenkovicGutmanFixedDegree04Class14
import Proofs.RadenkovicGutmanFixedDegree04Class10
import Proofs.RadenkovicGutmanFixedDegree04Class22
import Proofs.RadenkovicGutmanFixedDegree04Class23
import Proofs.RadenkovicGutmanFixedDegree04Class24
import Proofs.RadenkovicGutmanFixedDegree04Class20
import Proofs.RadenkovicGutmanFixedDegree04Class33
import Proofs.RadenkovicGutmanFixedDegree04Class34
import Proofs.RadenkovicGutmanFixedDegree04Class30
import Proofs.RadenkovicGutmanFixedDegree04Class44
import Proofs.RadenkovicGutmanFixedDegree04Class40
import Proofs.RadenkovicGutmanD4RefinedOriginalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree04ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeFourToFortyfiveDirectReserveAssembly.ClassCertificates 4 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree04Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree04Class11.reserve]
  · have hb := FixedDegree04Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree04Class12.reserve]
  · have hb := FixedDegree04Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree04Class13.reserve]
  · have hb := FixedDegree04Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree04Class14.reserve]
  · have hb := FixedDegree04Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree04Class10.reserve]
  · omega
  · have hb := FixedDegree04Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree04Class22.reserve]
  · have hb := FixedDegree04Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree04Class23.reserve]
  · have hb := FixedDegree04Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree04Class24.reserve]
  · have hb := FixedDegree04Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree04Class20.reserve]
  · omega
  · omega
  · have hb := FixedDegree04Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree04Class33.reserve]
  · have hb := FixedDegree04Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree04Class34.reserve]
  · have hb := FixedDegree04Class30.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree04Class30.reserve]
  · omega
  · omega
  · omega
  · have hb := FixedDegree04Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree04Class44.reserve]
  · have hb := FixedDegree04Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree04Class40.reserve]
  · omega
  · omega
  · omega
  · omega
  · have hb := D4RefinedOriginalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D4RefinedOriginalBothLong.reserve]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree04ClassCertificates
