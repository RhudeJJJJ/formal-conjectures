/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00724 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 512505970838597507165450141696000000000000 405354946225951073766167975620728437342208 3647508213322496402188866158592000000000000))
theorem leaf00724_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 512505970838597507165450141696000000000000 405354946225951073766167975620728437342208 3647508213322496402188866158592000000000000 raw00724=true := by decide +kernel
#print axioms leaf00724_raw
theorem leaf00724_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00724=true := by decide +kernel
#print axioms leaf00724_rectangular
def affine00724 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00724 (IntegerComputedClassCell.leftNumerator ![(197/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(197/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(197/6400),0,(1/2)] ![(3/6400),1,(1/2)]))
theorem leaf00724_transform : affine00724=(NestedInteger.clearedAll 3 raw00724 (IntegerComputedClassCell.leftNumerator ![(197/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(197/6400),0,(1/2)] ![(3/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(197/6400),0,(1/2)] ![(3/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00724_transform
theorem leaf00724_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00724=true := by decide +kernel
#print axioms leaf00724_sign
theorem leaf00724_log : RationalLog.accepts (1528624271/2147483648) (-729991143/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00724_log
def leaf00724 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (111132017399/1000000000000) (1528624271/2147483648) (-729991143/4294967296) 1 8 ![60,0,4] ![(197/6400),0,(1/2)] ![(3/6400),1,(1/2)] affine00724
theorem leaf00724_checked : FastNestedCellData.accepts 1 2 4 leaf00724=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (111132017399/1000000000000) (1528624271/2147483648) (-729991143/4294967296) 1 8 ![60,0,4] ![(197/6400),0,(1/2)] ![(3/6400),1,(1/2)] 512505970838597507165450141696000000000000 405354946225951073766167975620728437342208 3647508213322496402188866158592000000000000 raw00724 affine00724
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00724_raw leaf00724_rectangular
    leaf00724_transform leaf00724_sign leaf00724_log
#print axioms leaf00724_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
