/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00090 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1027305298472726839835311996928000000000000 1123540854845086350265777036485181046784 5043697972865655993859571712000000000000))
theorem leaf00090_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1027305298472726839835311996928000000000000 1123540854845086350265777036485181046784 5043697972865655993859571712000000000000 raw00090=true := by decide +kernel
#print axioms leaf00090_raw
theorem leaf00090_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00090=true := by decide +kernel
#print axioms leaf00090_rectangular
def affine00090 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00090 (IntegerComputedClassCell.leftNumerator ![(31/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/3200),0,0] ![(1/3200),1,(1/4)]))
theorem leaf00090_transform : affine00090=(NestedInteger.clearedAll 3 raw00090 (IntegerComputedClassCell.leftNumerator ![(31/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(31/3200),0,0] ![(1/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(31/3200),0,0] ![(1/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00090_transform
theorem leaf00090_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00090=true := by decide +kernel
#print axioms leaf00090_sign
theorem leaf00090_log : RationalLog.accepts (3841559/4294967296) (-3768469335/1073741824) 11 8=true := by decide +kernel
#print axioms leaf00090_log
def leaf00090 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (111380663641/500000000000) (3841559/4294967296) (-3768469335/1073741824) 11 8 ![52,0,4] ![(31/3200),0,0] ![(1/3200),1,(1/4)] affine00090
theorem leaf00090_checked : FastNestedCellData.accepts 1 0 4 leaf00090=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (111380663641/500000000000) (3841559/4294967296) (-3768469335/1073741824) 11 8 ![52,0,4] ![(31/3200),0,0] ![(1/3200),1,(1/4)] 1027305298472726839835311996928000000000000 1123540854845086350265777036485181046784 5043697972865655993859571712000000000000 raw00090 affine00090
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00090_raw leaf00090_rectangular
    leaf00090_transform leaf00090_sign leaf00090_log
#print axioms leaf00090_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
