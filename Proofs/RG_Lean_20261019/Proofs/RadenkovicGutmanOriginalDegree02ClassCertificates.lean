/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanDegreeTwoThreeDirectReserveAssembly
import Proofs.RadenkovicGutmanFixedDegree02Class11
import Proofs.RadenkovicGutmanFixedDegree02Class12
import Proofs.RadenkovicGutmanFixedDegree02Class13
import Proofs.RadenkovicGutmanFixedDegree02Class14
import Proofs.RadenkovicGutmanFixedDegree02Class10
import Proofs.RadenkovicGutmanFixedDegree02Class22
import Proofs.RadenkovicGutmanFixedDegree02Class23
import Proofs.RadenkovicGutmanFixedDegree02Class24
import Proofs.RadenkovicGutmanFixedDegree02Class20
import Proofs.RadenkovicGutmanFixedDegree02Class33
import Proofs.RadenkovicGutmanFixedDegree02Class34
import Proofs.RadenkovicGutmanD2OriginalShortLong
import Proofs.RadenkovicGutmanFixedDegree02Class44
import Proofs.RadenkovicGutmanFixedDegree02Class40
import Proofs.RadenkovicGutmanD2RefinedOriginalBothLong
namespace Gebendorfer.RadenkovicGutman.OriginalDegree02ClassCertificates
open ActualFusionIntegral
open scoped Classical
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
theorem certificates : DegreeTwoThreeDirectReserveAssembly.ClassCertificates 2 := by
  intro a b hab m C u p q hd hp hq
  fin_cases a <;> fin_cases b
  · have hb := FixedDegree02Class11.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree02Class11.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · have hb := FixedDegree02Class12.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree02Class12.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · have hb := FixedDegree02Class13.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree02Class13.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · have hb := FixedDegree02Class14.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree02Class14.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · have hb := FixedDegree02Class10.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree02Class10.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · omega
  · have hb := FixedDegree02Class22.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree02Class22.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · have hb := FixedDegree02Class23.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree02Class23.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · have hb := FixedDegree02Class24.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree02Class24.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · have hb := FixedDegree02Class20.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree02Class20.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · omega
  · omega
  · have hb := FixedDegree02Class33.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree02Class33.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · have hb := FixedDegree02Class34.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree02Class34.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · have hb := D2OriginalShortLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D2OriginalShortLong.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · omega
  · omega
  · omega
  · have hb := FixedDegree02Class44.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree02Class44.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · have hb := FixedDegree02Class40.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [FixedDegree02Class40.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
  · omega
  · omega
  · omega
  · omega
  · have hb := D2RefinedOriginalBothLong.normalized_target C u p q hd hp hq
    convert hb using 1 <;> norm_num [D2RefinedOriginalBothLong.reserve,DegreeTwoThreeClassAssembly.cutoff,DegreeTwoThreeThresholds.threshold2,DegreeTwoThreeThresholds.threshold3]
#print axioms certificates
end
end Gebendorfer.RadenkovicGutman.OriginalDegree02ClassCertificates
