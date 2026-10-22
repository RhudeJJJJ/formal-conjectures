/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00018 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 213764337159265962507693876838400000000000 4226326304407499319261519212206620672 72941970344946699815878656000000000000))
theorem leaf00018_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 213764337159265962507693876838400000000000 4226326304407499319261519212206620672 72941970344946699815878656000000000000 raw00018=true := by decide +kernel
#print axioms leaf00018_raw
theorem leaf00018_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00018=true := by decide +kernel
#print axioms leaf00018_rectangular
def affine00018 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00018 (IntegerComputedClassCell.leftNumerator ![(19/8000),0,0] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/8000),0,0] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/8000),0,0] ![(3/16000),1,(1/4)]))
theorem leaf00018_transform : affine00018=(NestedInteger.clearedAll 3 raw00018 (IntegerComputedClassCell.leftNumerator ![(19/8000),0,0] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(19/8000),0,0] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(19/8000),0,0] ![(3/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00018_transform
theorem leaf00018_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00018=true := by decide +kernel
#print axioms leaf00018_sign
theorem leaf00018_log : RationalLog.accepts (80265/4294967296) (-23380988281/4294967296) 16 8=true := by decide +kernel
#print axioms leaf00018_log
def leaf00018 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (57940939687/1000000000000) (80265/4294967296) (-23380988281/4294967296) 16 8 ![52,0,4] ![(19/8000),0,0] ![(3/16000),1,(1/4)] affine00018
theorem leaf00018_checked : FastNestedCellData.accepts 1 0 4 leaf00018=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (57940939687/1000000000000) (80265/4294967296) (-23380988281/4294967296) 16 8 ![52,0,4] ![(19/8000),0,0] ![(3/16000),1,(1/4)] 213764337159265962507693876838400000000000 4226326304407499319261519212206620672 72941970344946699815878656000000000000 raw00018 affine00018
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00018_raw leaf00018_rectangular
    leaf00018_transform leaf00018_sign leaf00018_log
#print axioms leaf00018_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
