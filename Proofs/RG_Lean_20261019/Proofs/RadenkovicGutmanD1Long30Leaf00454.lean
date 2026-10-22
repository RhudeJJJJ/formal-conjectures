/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00454 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 263149626868889623795872038912000000000000 238687451257336892559942809632414529224704 5577316575034639906519618945024000000000000))
theorem leaf00454_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 263149626868889623795872038912000000000000 238687451257336892559942809632414529224704 5577316575034639906519618945024000000000000 raw00454=true := by decide +kernel
#print axioms leaf00454_raw
theorem leaf00454_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00454=true := by decide +kernel
#print axioms leaf00454_rectangular
def affine00454 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00454 (IntegerComputedClassCell.leftNumerator ![(37/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(37/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(37/3200),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00454_transform : affine00454=(NestedInteger.clearedAll 3 raw00454 (IntegerComputedClassCell.leftNumerator ![(37/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(37/3200),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(37/3200),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00454_transform
theorem leaf00454_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00454=true := by decide +kernel
#print axioms leaf00454_sign
theorem leaf00454_log : RationalLog.accepts (3735831567/4294967296) (-74879277/1073741824) 1 8=true := by decide +kernel
#print axioms leaf00454_log
def leaf00454 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (42796109571/1000000000000) (3735831567/4294967296) (-74879277/1073741824) 1 8 ![60,0,4] ![(37/3200),0,(1/2)] ![(1/6400),1,(1/2)] affine00454
theorem leaf00454_checked : FastNestedCellData.accepts 1 2 4 leaf00454=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (42796109571/1000000000000) (3735831567/4294967296) (-74879277/1073741824) 1 8 ![60,0,4] ![(37/3200),0,(1/2)] ![(1/6400),1,(1/2)] 263149626868889623795872038912000000000000 238687451257336892559942809632414529224704 5577316575034639906519618945024000000000000 raw00454 affine00454
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00454_raw leaf00454_rectangular
    leaf00454_transform leaf00454_sign leaf00454_log
#print axioms leaf00454_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
