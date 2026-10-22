/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00288 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 51603588663947289060546969600000000000 46064950650087015564556004759464574976 935616258625247836896860569600000000000))
theorem leaf00288_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 51603588663947289060546969600000000000 46064950650087015564556004759464574976 935616258625247836896860569600000000000 raw00288=true := by decide +kernel
#print axioms leaf00288_raw
theorem leaf00288_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00288=true := by decide +kernel
#print axioms leaf00288_rectangular
def affine00288 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00288 (IntegerComputedClassCell.leftNumerator ![(41/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/6400),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00288_transform : affine00288=(NestedInteger.clearedAll 3 raw00288 (IntegerComputedClassCell.leftNumerator ![(41/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(41/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(41/6400),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00288_transform
theorem leaf00288_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00288=true := by decide +kernel
#print axioms leaf00288_sign
theorem leaf00288_log : RationalLog.accepts (456759787/536870912) (-347033513/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00288_log
def leaf00288 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (9846975237/200000000000) (456759787/536870912) (-347033513/4294967296) 1 8 ![60,0,4] ![(41/6400),0,(1/4)] ![(1/6400),1,(1/4)] affine00288
theorem leaf00288_checked : FastNestedCellData.accepts 1 2 4 leaf00288=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (9846975237/200000000000) (456759787/536870912) (-347033513/4294967296) 1 8 ![60,0,4] ![(41/6400),0,(1/4)] ![(1/6400),1,(1/4)] 51603588663947289060546969600000000000 46064950650087015564556004759464574976 935616258625247836896860569600000000000 raw00288 affine00288
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00288_raw leaf00288_rectangular
    leaf00288_transform leaf00288_sign leaf00288_log
#print axioms leaf00288_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
