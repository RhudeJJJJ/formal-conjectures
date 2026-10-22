/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00029 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 3176298345128101320304099328000000000000 3090199033425902865809207599115186208768 280417370475972149406402084864000000000000))
theorem leaf00029_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 3176298345128101320304099328000000000000 3090199033425902865809207599115186208768 280417370475972149406402084864000000000000 raw00029=true := by decide +kernel
#print axioms leaf00029_raw
theorem leaf00029_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00029=true := by decide +kernel
#print axioms leaf00029_rectangular
def affine00029 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00029 (IntegerComputedClassCell.leftNumerator ![(47/16000),0,(1/2)] ![(3/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(47/16000),0,(1/2)] ![(3/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(47/16000),0,(1/2)] ![(3/16000),1,(1/2)]))
theorem leaf00029_transform : affine00029=(NestedInteger.clearedAll 3 raw00029 (IntegerComputedClassCell.leftNumerator ![(47/16000),0,(1/2)] ![(3/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(47/16000),0,(1/2)] ![(3/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(47/16000),0,(1/2)] ![(3/16000),1,(1/2)])) := by decide +kernel
#print axioms leaf00029_transform
theorem leaf00029_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00029=true := by decide +kernel
#print axioms leaf00029_sign
theorem leaf00029_log : RationalLog.accepts (2066499399/2147483648) (-82550803/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00029_log
def leaf00029 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (2754999653/250000000000) (2066499399/2147483648) (-82550803/4294967296) 1 8 ![52,0,4] ![(47/16000),0,(1/2)] ![(3/16000),1,(1/2)] affine00029
theorem leaf00029_checked : FastNestedCellData.accepts 1 0 4 leaf00029=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (2754999653/250000000000) (2066499399/2147483648) (-82550803/4294967296) 1 8 ![52,0,4] ![(47/16000),0,(1/2)] ![(3/16000),1,(1/2)] 3176298345128101320304099328000000000000 3090199033425902865809207599115186208768 280417370475972149406402084864000000000000 raw00029 affine00029
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00029_raw leaf00029_rectangular
    leaf00029_transform leaf00029_sign leaf00029_log
#print axioms leaf00029_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
