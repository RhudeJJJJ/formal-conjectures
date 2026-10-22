/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00027 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 81916658185526213123887857664000000000000 3000973790540167888283953691839430656 42236674377502961019387904000000000000))
theorem leaf00027_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 81916658185526213123887857664000000000000 3000973790540167888283953691839430656 42236674377502961019387904000000000000 raw00027=true := by decide +kernel
#print axioms leaf00027_raw
theorem leaf00027_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00027=true := by decide +kernel
#print axioms leaf00027_rectangular
def affine00027 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00027 (IntegerComputedClassCell.leftNumerator ![(47/16000),0,0] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(47/16000),0,0] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(47/16000),0,0] ![(3/16000),1,(1/4)]))
theorem leaf00027_transform : affine00027=(NestedInteger.clearedAll 3 raw00027 (IntegerComputedClassCell.leftNumerator ![(47/16000),0,0] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(47/16000),0,0] ![(3/16000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(47/16000),0,0] ![(3/16000),1,(1/4)])) := by decide +kernel
#print axioms leaf00027_transform
theorem leaf00027_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00027=true := by decide +kernel
#print axioms leaf00027_sign
theorem leaf00027_log : RationalLog.accepts (73453/2147483648) (-172522827/33554432) 15 8=true := by decide +kernel
#print axioms leaf00027_log
def leaf00027 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (35525687507/500000000000) (73453/2147483648) (-172522827/33554432) 15 8 ![52,0,4] ![(47/16000),0,0] ![(3/16000),1,(1/4)] affine00027
theorem leaf00027_checked : FastNestedCellData.accepts 1 0 4 leaf00027=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (35525687507/500000000000) (73453/2147483648) (-172522827/33554432) 15 8 ![52,0,4] ![(47/16000),0,0] ![(3/16000),1,(1/4)] 81916658185526213123887857664000000000000 3000973790540167888283953691839430656 42236674377502961019387904000000000000 raw00027 affine00027
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00027_raw leaf00027_rectangular
    leaf00027_transform leaf00027_sign leaf00027_log
#print axioms leaf00027_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
