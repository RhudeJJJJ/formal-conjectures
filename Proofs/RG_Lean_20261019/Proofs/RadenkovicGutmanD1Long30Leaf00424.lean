/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00424 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 567461855495844508441614745600000000000 518530831018254771746319938205429792768 13168844304086066701497532416000000000000))
theorem leaf00424_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 567461855495844508441614745600000000000 518530831018254771746319938205429792768 13168844304086066701497532416000000000000 raw00424=true := by decide +kernel
#print axioms leaf00424_raw
theorem leaf00424_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00424=true := by decide +kernel
#print axioms leaf00424_rectangular
def affine00424 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00424 (IntegerComputedClassCell.leftNumerator ![(17/1600),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/1600),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/1600),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00424_transform : affine00424=(NestedInteger.clearedAll 3 raw00424 (IntegerComputedClassCell.leftNumerator ![(17/1600),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(17/1600),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(17/1600),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00424_transform
theorem leaf00424_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00424=true := by decide +kernel
#print axioms leaf00424_sign
theorem leaf00424_log : RationalLog.accepts (471992695/536870912) (-276583409/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00424_log
def leaf00424 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (19687788049/500000000000) (471992695/536870912) (-276583409/4294967296) 1 8 ![60,0,4] ![(17/1600),0,(1/2)] ![(1/6400),1,(1/2)] affine00424
theorem leaf00424_checked : FastNestedCellData.accepts 1 2 4 leaf00424=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (19687788049/500000000000) (471992695/536870912) (-276583409/4294967296) 1 8 ![60,0,4] ![(17/1600),0,(1/2)] ![(1/6400),1,(1/2)] 567461855495844508441614745600000000000 518530831018254771746319938205429792768 13168844304086066701497532416000000000000 raw00424 affine00424
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00424_raw leaf00424_rectangular
    leaf00424_transform leaf00424_sign leaf00424_log
#print axioms leaf00424_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
