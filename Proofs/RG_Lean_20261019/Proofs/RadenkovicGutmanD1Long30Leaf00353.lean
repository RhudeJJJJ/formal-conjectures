/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00353 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 1189767441604389842214193201152000000000000 1027480328158675004953416975650970742554624 15930564235944587656156300705792000000000000))
theorem leaf00353_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 1189767441604389842214193201152000000000000 1027480328158675004953416975650970742554624 15930564235944587656156300705792000000000000 raw00353=true := by decide +kernel
#print axioms leaf00353_raw
theorem leaf00353_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00353=true := by decide +kernel
#print axioms leaf00353_rectangular
def affine00353 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00353 (IntegerComputedClassCell.leftNumerator ![(27/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(27/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(27/3200),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00353_transform : affine00353=(NestedInteger.clearedAll 3 raw00353 (IntegerComputedClassCell.leftNumerator ![(27/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(27/3200),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(27/3200),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00353_transform
theorem leaf00353_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00353=true := by decide +kernel
#print axioms leaf00353_sign
theorem leaf00353_log : RationalLog.accepts (3484389391/4294967296) (-112287163/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00353_log
def leaf00353 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (64497422247/1000000000000) (3484389391/4294967296) (-112287163/1073741824) 1 8 ![60,0,4] ![(27/3200),0,(1/4)] ![(1/6400),1,(1/4)] affine00353
theorem leaf00353_checked : FastNestedCellData.accepts 1 2 4 leaf00353=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (64497422247/1000000000000) (3484389391/4294967296) (-112287163/1073741824) 1 8 ![60,0,4] ![(27/3200),0,(1/4)] ![(1/6400),1,(1/4)] 1189767441604389842214193201152000000000000 1027480328158675004953416975650970742554624 15930564235944587656156300705792000000000000 raw00353 affine00353
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00353_raw leaf00353_rectangular
    leaf00353_transform leaf00353_sign leaf00353_log
#print axioms leaf00353_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
