/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00026 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 50507029052952878096842752000000000000 49215687607754520333586212405821571072 4760356423796930569123659776000000000000))
theorem leaf00026_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 50507029052952878096842752000000000000 49215687607754520333586212405821571072 4760356423796930569123659776000000000000 raw00026=true := by decide +kernel
#print axioms leaf00026_raw
theorem leaf00026_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00026=true := by decide +kernel
#print axioms leaf00026_rectangular
def affine00026 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00026 (IntegerComputedClassCell.leftNumerator ![(11/4000),0,(1/2)] ![(3/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/4000),0,(1/2)] ![(3/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/4000),0,(1/2)] ![(3/16000),1,(1/2)]))
theorem leaf00026_transform : affine00026=(NestedInteger.clearedAll 3 raw00026 (IntegerComputedClassCell.leftNumerator ![(11/4000),0,(1/2)] ![(3/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(11/4000),0,(1/2)] ![(3/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(11/4000),0,(1/2)] ![(3/16000),1,(1/2)])) := by decide +kernel
#print axioms leaf00026_transform
theorem leaf00026_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00026=true := by decide +kernel
#print axioms leaf00026_sign
theorem leaf00026_log : RationalLog.accepts (1035582337/1073741824) (-77708165/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00026_log
def leaf00026 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (5169328011/500000000000) (1035582337/1073741824) (-77708165/4294967296) 1 8 ![52,0,4] ![(11/4000),0,(1/2)] ![(3/16000),1,(1/2)] affine00026
theorem leaf00026_checked : FastNestedCellData.accepts 1 0 4 leaf00026=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (5169328011/500000000000) (1035582337/1073741824) (-77708165/4294967296) 1 8 ![52,0,4] ![(11/4000),0,(1/2)] ![(3/16000),1,(1/2)] 50507029052952878096842752000000000000 49215687607754520333586212405821571072 4760356423796930569123659776000000000000 raw00026 affine00026
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00026_raw leaf00026_rectangular
    leaf00026_transform leaf00026_sign leaf00026_log
#print axioms leaf00026_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
