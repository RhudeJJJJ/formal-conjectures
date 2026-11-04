/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanIntegerPiecewiseCell
import Proofs.RadenkovicGutmanIntegerWeightedOuter
import Proofs.RadenkovicGutmanIntegerWeightedBernstein
import Proofs.RadenkovicGutmanD1IntegerNorm00
import Proofs.RadenkovicGutmanIntegerBernsteinWeights88
import Proofs.RadenkovicGutmanD1Long00Leaf01668Rows00
import Proofs.RadenkovicGutmanD1Long00Leaf01668Rows01
import Proofs.RadenkovicGutmanD1Long00Leaf01668Rows02
import Proofs.RadenkovicGutmanD1Long00Leaf01668Rows03
import Proofs.RadenkovicGutmanD1Long00Leaf01668Rows04
import Proofs.RadenkovicGutmanD1Long00Leaf01668Rows05
import Proofs.RadenkovicGutmanD1Long00Leaf01668Rows06
import Proofs.RadenkovicGutmanD1Long00Leaf01668Rows07
import Proofs.RadenkovicGutmanD1Long00Leaf01668Rows08

/-!
# Original leaf 01668 — complete certificate

Every declaration, datum, type and proof body below is retained verbatim.
Only module boundaries and imports are changed to keep the original
kernel checks within the fixed resource limits.
Source: [original leaf certificate](https://github.com/RhudeJJJJ/formal-conjectures/blob/aaeaec3cec22467d3f0b83b1761bfb40087bb991/Proofs/RG_Lean_20261019/Proofs/RadenkovicGutmanD1Long00Leaf01668.lean).
-/
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open NestedInteger NestedHorner
def leaf01668_w_rows : Fin 89 → NestedInteger.Poly 2 := ![leaf01668_w_row000,leaf01668_w_row001,leaf01668_w_row002,leaf01668_w_row003,leaf01668_w_row004,leaf01668_w_row005,leaf01668_w_row006,leaf01668_w_row007,leaf01668_w_row008,leaf01668_w_row009,leaf01668_w_row010,leaf01668_w_row011,leaf01668_w_row012,leaf01668_w_row013,leaf01668_w_row014,leaf01668_w_row015,leaf01668_w_row016,leaf01668_w_row017,leaf01668_w_row018,leaf01668_w_row019,leaf01668_w_row020,leaf01668_w_row021,leaf01668_w_row022,leaf01668_w_row023,leaf01668_w_row024,leaf01668_w_row025,leaf01668_w_row026,leaf01668_w_row027,leaf01668_w_row028,leaf01668_w_row029,leaf01668_w_row030,leaf01668_w_row031,leaf01668_w_row032,leaf01668_w_row033,leaf01668_w_row034,leaf01668_w_row035,leaf01668_w_row036,leaf01668_w_row037,leaf01668_w_row038,leaf01668_w_row039,leaf01668_w_row040,leaf01668_w_row041,leaf01668_w_row042,leaf01668_w_row043,leaf01668_w_row044,leaf01668_w_row045,leaf01668_w_row046,leaf01668_w_row047,leaf01668_w_row048,leaf01668_w_row049,leaf01668_w_row050,leaf01668_w_row051,leaf01668_w_row052,leaf01668_w_row053,leaf01668_w_row054,leaf01668_w_row055,leaf01668_w_row056,leaf01668_w_row057,leaf01668_w_row058,leaf01668_w_row059,leaf01668_w_row060,leaf01668_w_row061,leaf01668_w_row062,leaf01668_w_row063,leaf01668_w_row064,leaf01668_w_row065,leaf01668_w_row066,leaf01668_w_row067,leaf01668_w_row068,leaf01668_w_row069,leaf01668_w_row070,leaf01668_w_row071,leaf01668_w_row072,leaf01668_w_row073,leaf01668_w_row074,leaf01668_w_row075,leaf01668_w_row076,leaf01668_w_row077,leaf01668_w_row078,leaf01668_w_row079,leaf01668_w_row080,leaf01668_w_row081,leaf01668_w_row082,leaf01668_w_row083,leaf01668_w_row084,leaf01668_w_row085,leaf01668_w_row086,leaf01668_w_row087,leaf01668_w_row088]
theorem leaf01668_sign : NestedInteger.bernsteinCheck 3 ![88,4,4] leaf01668_w_affine=true := by
  apply IntegerBernsteinRows.checked ![88,4,4] leaf01668_w_affine leaf01668_w_rows (by decide +kernel)
  · intro j
    fin_cases j
    · exact leaf01668_w_row000_identity
    · exact leaf01668_w_row001_identity
    · exact leaf01668_w_row002_identity
    · exact leaf01668_w_row003_identity
    · exact leaf01668_w_row004_identity
    · exact leaf01668_w_row005_identity
    · exact leaf01668_w_row006_identity
    · exact leaf01668_w_row007_identity
    · exact leaf01668_w_row008_identity
    · exact leaf01668_w_row009_identity
    · exact leaf01668_w_row010_identity
    · exact leaf01668_w_row011_identity
    · exact leaf01668_w_row012_identity
    · exact leaf01668_w_row013_identity
    · exact leaf01668_w_row014_identity
    · exact leaf01668_w_row015_identity
    · exact leaf01668_w_row016_identity
    · exact leaf01668_w_row017_identity
    · exact leaf01668_w_row018_identity
    · exact leaf01668_w_row019_identity
    · exact leaf01668_w_row020_identity
    · exact leaf01668_w_row021_identity
    · exact leaf01668_w_row022_identity
    · exact leaf01668_w_row023_identity
    · exact leaf01668_w_row024_identity
    · exact leaf01668_w_row025_identity
    · exact leaf01668_w_row026_identity
    · exact leaf01668_w_row027_identity
    · exact leaf01668_w_row028_identity
    · exact leaf01668_w_row029_identity
    · exact leaf01668_w_row030_identity
    · exact leaf01668_w_row031_identity
    · exact leaf01668_w_row032_identity
    · exact leaf01668_w_row033_identity
    · exact leaf01668_w_row034_identity
    · exact leaf01668_w_row035_identity
    · exact leaf01668_w_row036_identity
    · exact leaf01668_w_row037_identity
    · exact leaf01668_w_row038_identity
    · exact leaf01668_w_row039_identity
    · exact leaf01668_w_row040_identity
    · exact leaf01668_w_row041_identity
    · exact leaf01668_w_row042_identity
    · exact leaf01668_w_row043_identity
    · exact leaf01668_w_row044_identity
    · exact leaf01668_w_row045_identity
    · exact leaf01668_w_row046_identity
    · exact leaf01668_w_row047_identity
    · exact leaf01668_w_row048_identity
    · exact leaf01668_w_row049_identity
    · exact leaf01668_w_row050_identity
    · exact leaf01668_w_row051_identity
    · exact leaf01668_w_row052_identity
    · exact leaf01668_w_row053_identity
    · exact leaf01668_w_row054_identity
    · exact leaf01668_w_row055_identity
    · exact leaf01668_w_row056_identity
    · exact leaf01668_w_row057_identity
    · exact leaf01668_w_row058_identity
    · exact leaf01668_w_row059_identity
    · exact leaf01668_w_row060_identity
    · exact leaf01668_w_row061_identity
    · exact leaf01668_w_row062_identity
    · exact leaf01668_w_row063_identity
    · exact leaf01668_w_row064_identity
    · exact leaf01668_w_row065_identity
    · exact leaf01668_w_row066_identity
    · exact leaf01668_w_row067_identity
    · exact leaf01668_w_row068_identity
    · exact leaf01668_w_row069_identity
    · exact leaf01668_w_row070_identity
    · exact leaf01668_w_row071_identity
    · exact leaf01668_w_row072_identity
    · exact leaf01668_w_row073_identity
    · exact leaf01668_w_row074_identity
    · exact leaf01668_w_row075_identity
    · exact leaf01668_w_row076_identity
    · exact leaf01668_w_row077_identity
    · exact leaf01668_w_row078_identity
    · exact leaf01668_w_row079_identity
    · exact leaf01668_w_row080_identity
    · exact leaf01668_w_row081_identity
    · exact leaf01668_w_row082_identity
    · exact leaf01668_w_row083_identity
    · exact leaf01668_w_row084_identity
    · exact leaf01668_w_row085_identity
    · exact leaf01668_w_row086_identity
    · exact leaf01668_w_row087_identity
    · exact leaf01668_w_row088_identity
  · intro j
    fin_cases j
    · exact leaf01668_w_row000_positive
    · exact leaf01668_w_row001_positive
    · exact leaf01668_w_row002_positive
    · exact leaf01668_w_row003_positive
    · exact leaf01668_w_row004_positive
    · exact leaf01668_w_row005_positive
    · exact leaf01668_w_row006_positive
    · exact leaf01668_w_row007_positive
    · exact leaf01668_w_row008_positive
    · exact leaf01668_w_row009_positive
    · exact leaf01668_w_row010_positive
    · exact leaf01668_w_row011_positive
    · exact leaf01668_w_row012_positive
    · exact leaf01668_w_row013_positive
    · exact leaf01668_w_row014_positive
    · exact leaf01668_w_row015_positive
    · exact leaf01668_w_row016_positive
    · exact leaf01668_w_row017_positive
    · exact leaf01668_w_row018_positive
    · exact leaf01668_w_row019_positive
    · exact leaf01668_w_row020_positive
    · exact leaf01668_w_row021_positive
    · exact leaf01668_w_row022_positive
    · exact leaf01668_w_row023_positive
    · exact leaf01668_w_row024_positive
    · exact leaf01668_w_row025_positive
    · exact leaf01668_w_row026_positive
    · exact leaf01668_w_row027_positive
    · exact leaf01668_w_row028_positive
    · exact leaf01668_w_row029_positive
    · exact leaf01668_w_row030_positive
    · exact leaf01668_w_row031_positive
    · exact leaf01668_w_row032_positive
    · exact leaf01668_w_row033_positive
    · exact leaf01668_w_row034_positive
    · exact leaf01668_w_row035_positive
    · exact leaf01668_w_row036_positive
    · exact leaf01668_w_row037_positive
    · exact leaf01668_w_row038_positive
    · exact leaf01668_w_row039_positive
    · exact leaf01668_w_row040_positive
    · exact leaf01668_w_row041_positive
    · exact leaf01668_w_row042_positive
    · exact leaf01668_w_row043_positive
    · exact leaf01668_w_row044_positive
    · exact leaf01668_w_row045_positive
    · exact leaf01668_w_row046_positive
    · exact leaf01668_w_row047_positive
    · exact leaf01668_w_row048_positive
    · exact leaf01668_w_row049_positive
    · exact leaf01668_w_row050_positive
    · exact leaf01668_w_row051_positive
    · exact leaf01668_w_row052_positive
    · exact leaf01668_w_row053_positive
    · exact leaf01668_w_row054_positive
    · exact leaf01668_w_row055_positive
    · exact leaf01668_w_row056_positive
    · exact leaf01668_w_row057_positive
    · exact leaf01668_w_row058_positive
    · exact leaf01668_w_row059_positive
    · exact leaf01668_w_row060_positive
    · exact leaf01668_w_row061_positive
    · exact leaf01668_w_row062_positive
    · exact leaf01668_w_row063_positive
    · exact leaf01668_w_row064_positive
    · exact leaf01668_w_row065_positive
    · exact leaf01668_w_row066_positive
    · exact leaf01668_w_row067_positive
    · exact leaf01668_w_row068_positive
    · exact leaf01668_w_row069_positive
    · exact leaf01668_w_row070_positive
    · exact leaf01668_w_row071_positive
    · exact leaf01668_w_row072_positive
    · exact leaf01668_w_row073_positive
    · exact leaf01668_w_row074_positive
    · exact leaf01668_w_row075_positive
    · exact leaf01668_w_row076_positive
    · exact leaf01668_w_row077_positive
    · exact leaf01668_w_row078_positive
    · exact leaf01668_w_row079_positive
    · exact leaf01668_w_row080_positive
    · exact leaf01668_w_row081_positive
    · exact leaf01668_w_row082_positive
    · exact leaf01668_w_row083_positive
    · exact leaf01668_w_row084_positive
    · exact leaf01668_w_row085_positive
    · exact leaf01668_w_row086_positive
    · exact leaf01668_w_row087_positive
    · exact leaf01668_w_row088_positive
#print axioms leaf01668_sign
theorem leaf01668_log : RationalLog.accepts (272794341/268435456) (34590987/4294967296) 0 8=true := by decide +kernel
#print axioms leaf01668_log
def leaf01668 : FastNestedCellData.Cell := IntegerScaledCell.make DegreeOneNormPack00.pack true (89717579/200000000000) (272794341/268435456) (34590987/4294967296) 0 8 ![88,4,4] ![(3/32),(1/2),(1/2)] ![(1/128),(1/4),(1/2)] 4816675846016204800000000000 ![128,4,2] leaf01668_w_affine
theorem leaf01668_checked : FastNestedCellData.accepts 1 4 4 leaf01668=true :=
  IntegerPiecewiseCell.accepts_make DegreeOneIntegerNorm00.pack true (89717579/200000000000) (272794341/268435456) (34590987/4294967296) 0 8 ![88,4,4] ![(3/32),(1/2),(1/2)] ![(1/128),(1/4),(1/2)]
    4816675846016204800000000000 4897085356091602382550197181 10916668529567884087800000000000 ![12,2,1] ![1,1,1] ![128,4,2] leaf01668_w_raw leaf01668_w_inner leaf01668_w_affine
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    leaf01668_raw leaf01668_rectangular leaf01668_inner leaf01668_w_affine_eval leaf01668_sign leaf01668_log
#print axioms leaf01668_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass00
