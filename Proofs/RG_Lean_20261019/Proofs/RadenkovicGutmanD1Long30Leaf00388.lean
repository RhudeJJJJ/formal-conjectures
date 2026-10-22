/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00388 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 20944067876605916059495563264000000000000 17774091982105019902175210011606697115648 244605453340779808982206251008000000000000))
theorem leaf00388_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 20944067876605916059495563264000000000000 17774091982105019902175210011606697115648 244605453340779808982206251008000000000000 raw00388=true := by decide +kernel
#print axioms leaf00388_raw
theorem leaf00388_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00388=true := by decide +kernel
#print axioms leaf00388_rectangular
def affine00388 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00388 (IntegerComputedClassCell.leftNumerator ![(61/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(61/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(61/6400),0,(1/4)] ![(1/6400),1,(1/4)]))
theorem leaf00388_transform : affine00388=(NestedInteger.clearedAll 3 raw00388 (IntegerComputedClassCell.leftNumerator ![(61/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(61/6400),0,(1/4)] ![(1/6400),1,(1/4)]) (IntegerComputedClassCell.denominator ![(61/6400),0,(1/4)] ![(1/6400),1,(1/4)])) := by decide +kernel
#print axioms leaf00388_transform
theorem leaf00388_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00388=true := by decide +kernel
#print axioms leaf00388_sign
theorem leaf00388_log : RationalLog.accepts (3397992437/4294967296) (-125766929/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00388_log
def leaf00388 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (9083041557/125000000000) (3397992437/4294967296) (-125766929/1073741824) 1 8 ![60,0,4] ![(61/6400),0,(1/4)] ![(1/6400),1,(1/4)] affine00388
theorem leaf00388_checked : FastNestedCellData.accepts 1 2 4 leaf00388=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (9083041557/125000000000) (3397992437/4294967296) (-125766929/1073741824) 1 8 ![60,0,4] ![(61/6400),0,(1/4)] ![(1/6400),1,(1/4)] 20944067876605916059495563264000000000000 17774091982105019902175210011606697115648 244605453340779808982206251008000000000000 raw00388 affine00388
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00388_raw leaf00388_rectangular
    leaf00388_transform leaf00388_sign leaf00388_log
#print axioms leaf00388_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
