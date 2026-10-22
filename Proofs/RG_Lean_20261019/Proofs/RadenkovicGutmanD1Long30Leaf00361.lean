/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00361 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3043480941322423866321849548800000000000 1702000214192188640015094762027664539648 6447461592892401180170885529600000000000))
theorem leaf00361_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3043480941322423866321849548800000000000 1702000214192188640015094762027664539648 6447461592892401180170885529600000000000 raw00361=true := by decide +kernel
#print axioms leaf00361_raw
theorem leaf00361_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00361=true := by decide +kernel
#print axioms leaf00361_rectangular
def affine00361 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00361 (IntegerComputedClassCell.leftNumerator ![(7/800),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/800),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/800),0,(1/16)] ![(1/6400),1,(1/16)]))
theorem leaf00361_transform : affine00361=(NestedInteger.clearedAll 3 raw00361 (IntegerComputedClassCell.leftNumerator ![(7/800),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/800),0,(1/16)] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/800),0,(1/16)] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00361_transform
theorem leaf00361_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00361=true := by decide +kernel
#print axioms leaf00361_sign
theorem leaf00361_log : RationalLog.accepts (1900241157/4294967296) (-875596913/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00361_log
def leaf00361 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (6599497297/25000000000) (1900241157/4294967296) (-875596913/2147483648) 2 8 ![60,0,4] ![(7/800),0,(1/16)] ![(1/6400),1,(1/16)] affine00361
theorem leaf00361_checked : FastNestedCellData.accepts 1 2 4 leaf00361=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (6599497297/25000000000) (1900241157/4294967296) (-875596913/2147483648) 2 8 ![60,0,4] ![(7/800),0,(1/16)] ![(1/6400),1,(1/16)] 3043480941322423866321849548800000000000 1702000214192188640015094762027664539648 6447461592892401180170885529600000000000 raw00361 affine00361
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00361_raw leaf00361_rectangular
    leaf00361_transform leaf00361_sign leaf00361_log
#print axioms leaf00361_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
