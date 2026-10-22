/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00840 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 645448954790169587046258678169600000000000 58044883010376018690732871643588525555712 66356237390075686351715224780800000000000))
theorem leaf00840_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 645448954790169587046258678169600000000000 58044883010376018690732871643588525555712 66356237390075686351715224780800000000000 raw00840=true := by decide +kernel
#print axioms leaf00840_raw
theorem leaf00840_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00840=true := by decide +kernel
#print axioms leaf00840_rectangular
def affine00840 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00840 (IntegerComputedClassCell.leftNumerator ![(1/20),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/20),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/20),0,0] ![(1/640),1,(1/16)]))
theorem leaf00840_transform : affine00840=(NestedInteger.clearedAll 3 raw00840 (IntegerComputedClassCell.leftNumerator ![(1/20),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(1/20),0,0] ![(1/640),1,(1/16)]) (IntegerComputedClassCell.denominator ![(1/20),0,0] ![(1/640),1,(1/16)])) := by decide +kernel
#print axioms leaf00840_transform
theorem leaf00840_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00840=true := by decide +kernel
#print axioms leaf00840_sign
theorem leaf00840_log : RationalLog.accepts (206024733/4294967296) (-6522343945/4294967296) 5 8=true := by decide +kernel
#print axioms leaf00840_log
def leaf00840 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (174949289753/200000000000) (206024733/4294967296) (-6522343945/4294967296) 5 8 ![60,0,4] ![(1/20),0,0] ![(1/640),1,(1/16)] affine00840
theorem leaf00840_checked : FastNestedCellData.accepts 1 2 4 leaf00840=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (174949289753/200000000000) (206024733/4294967296) (-6522343945/4294967296) 5 8 ![60,0,4] ![(1/20),0,0] ![(1/640),1,(1/16)] 645448954790169587046258678169600000000000 58044883010376018690732871643588525555712 66356237390075686351715224780800000000000 raw00840 affine00840
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00840_raw leaf00840_rectangular
    leaf00840_transform leaf00840_sign leaf00840_log
#print axioms leaf00840_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
