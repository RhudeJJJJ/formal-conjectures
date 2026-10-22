/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00010 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 87356814497866435947814453248000000000000 84165173192416759649005200389275524268032 5924259863504490340943342338048000000000000))
theorem leaf00010_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 87356814497866435947814453248000000000000 84165173192416759649005200389275524268032 5924259863504490340943342338048000000000000 raw00010=true := by decide +kernel
#print axioms leaf00010_raw
theorem leaf00010_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00010=true := by decide +kernel
#print axioms leaf00010_rectangular
def affine00010 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00010 (IntegerComputedClassCell.leftNumerator ![(7/4000),0,(1/4)] ![(1/4000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/4000),0,(1/4)] ![(1/4000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/4000),0,(1/4)] ![(1/4000),1,(1/4)]))
theorem leaf00010_transform : affine00010=(NestedInteger.clearedAll 3 raw00010 (IntegerComputedClassCell.leftNumerator ![(7/4000),0,(1/4)] ![(1/4000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(7/4000),0,(1/4)] ![(1/4000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(7/4000),0,(1/4)] ![(1/4000),1,(1/4)])) := by decide +kernel
#print axioms leaf00010_transform
theorem leaf00010_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00010=true := by decide +kernel
#print axioms leaf00010_sign
theorem leaf00010_log : RationalLog.accepts (4080082521/4294967296) (-110223343/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00010_log
def leaf00010 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (14206867209/1000000000000) (4080082521/4294967296) (-110223343/4294967296) 1 8 ![52,0,4] ![(7/4000),0,(1/4)] ![(1/4000),1,(1/4)] affine00010
theorem leaf00010_checked : FastNestedCellData.accepts 1 0 4 leaf00010=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (14206867209/1000000000000) (4080082521/4294967296) (-110223343/4294967296) 1 8 ![52,0,4] ![(7/4000),0,(1/4)] ![(1/4000),1,(1/4)] 87356814497866435947814453248000000000000 84165173192416759649005200389275524268032 5924259863504490340943342338048000000000000 raw00010 affine00010
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00010_raw leaf00010_rectangular
    leaf00010_transform leaf00010_sign leaf00010_log
#print axioms leaf00010_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
