/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree03Class11
import Proofs.RadenkovicGutmanFixedDegree03Class12
import Proofs.RadenkovicGutmanFixedDegree03Class13
import Proofs.RadenkovicGutmanFixedDegree03Class14
import Proofs.RadenkovicGutmanFixedDegree03Class10
import Proofs.RadenkovicGutmanFixedDegree03Class22
import Proofs.RadenkovicGutmanFixedDegree03Class23
import Proofs.RadenkovicGutmanFixedDegree03Class24
import Proofs.RadenkovicGutmanFixedDegree03Class20
import Proofs.RadenkovicGutmanFixedDegree03Class33
import Proofs.RadenkovicGutmanFixedDegree03Class34
import Proofs.RadenkovicGutmanFixedDegree03Class30ParameterDepth1
import Proofs.RadenkovicGutmanFixedDegree03Class44
import Proofs.RadenkovicGutmanFixedDegree03Class40
import Proofs.RadenkovicGutmanD3RefinedOriginalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree03ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeTwoThreeDirectReserveAssembly.ClassCertificates 3 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree03Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree03Class11.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · have hb := FixedDegree03Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree03Class12.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · have hb := FixedDegree03Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree03Class13.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · have hb := FixedDegree03Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree03Class14.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · have hb := FixedDegree03Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree03Class10.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · omega
  · have hb := FixedDegree03Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree03Class22.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · have hb := FixedDegree03Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree03Class23.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · have hb := FixedDegree03Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree03Class24.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · have hb := FixedDegree03Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree03Class20.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · omega
  · omega
  · have hb := FixedDegree03Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree03Class33.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · have hb := FixedDegree03Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree03Class34.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · have hb := FixedDegree03Class30ParameterDepth1.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree03Class30ParameterDepth1.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · omega
  · omega
  · omega
  · have hb := FixedDegree03Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree03Class44.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · have hb := FixedDegree03Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree03Class40.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · omega
  · omega
  · omega
  · omega
  · have hb := D3RefinedOriginalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D3RefinedOriginalBothLong.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree03ClassCertificates
