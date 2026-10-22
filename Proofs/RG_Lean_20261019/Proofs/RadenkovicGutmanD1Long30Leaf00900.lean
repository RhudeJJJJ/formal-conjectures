/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00900 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 5091149369081391590420774912000000000000 817093771635920149357389245988024090624 963728211109298689441529856000000000000))
theorem leaf00900_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 5091149369081391590420774912000000000000 817093771635920149357389245988024090624 963728211109298689441529856000000000000 raw00900=true := by decide +kernel
#print axioms leaf00900_raw
theorem leaf00900_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00900=true := by decide +kernel
#print axioms leaf00900_rectangular
def affine00900 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00900 (IntegerComputedClassCell.leftNumerator ![(11/160),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/160),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/160),0,0] ![(1/640),1,(1/16)]))
theorem leaf00900_transform : affine00900=(NestedInteger.clearedAll 3 raw00900 (IntegerComputedClassCell.leftNumerator ![(11/160),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(11/160),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(11/160),0,0] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00900_transform
theorem leaf00900_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00900=true := by decide +kernel
#print axioms leaf00900_sign
theorem leaf00900_log : RationalLog.accepts (93258837/1073741824) (-163982261/134217728) 4 8=true := by decide +kernel
#print axioms leaf00900_log
def leaf00900 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (105980835963/125000000000) (93258837/1073741824) (-163982261/134217728) 4 8 ![60,0,4] ![(11/160),0,0] ![(1/640),1,(1/16)] affine00900
theorem leaf00900_checked : FastNestedCellData.accepts 1 2 4 leaf00900=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (105980835963/125000000000) (93258837/1073741824) (-163982261/134217728) 4 8 ![60,0,4] ![(11/160),0,0] ![(1/640),1,(1/16)] 5091149369081391590420774912000000000000 817093771635920149357389245988024090624 963728211109298689441529856000000000000 raw00900 affine00900
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00900_raw leaf00900_rectangular
    leaf00900_transform leaf00900_sign leaf00900_log
#print axioms leaf00900_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
