/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00557 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 45916070216383540244142075412480000000000 26965156584523791031400092403943151239168 108332298491156083074196832256000000000000))
theorem leaf00557_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 45916070216383540244142075412480000000000 26965156584523791031400092403943151239168 108332298491156083074196832256000000000000 raw00557=true := by decide +kernel
#print axioms leaf00557_raw
theorem leaf00557_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00557=true := by decide +kernel
#print axioms leaf00557_rectangular
def affine00557 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00557 (IntegerComputedClassCell.leftNumerator ![(27/1600),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(27/1600),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(27/1600),0,(1/8)] ![(1/3200),1,(1/8)]))
theorem leaf00557_transform : affine00557=(NestedInteger.clearedAll 3 raw00557 (IntegerComputedClassCell.leftNumerator ![(27/1600),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(27/1600),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(27/1600),0,(1/8)] ![(1/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00557_transform
theorem leaf00557_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00557=true := by decide +kernel
#print axioms leaf00557_sign
theorem leaf00557_log : RationalLog.accepts (1009802475/2147483648) (-1620366717/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00557_log
def leaf00557 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (248911515403/1000000000000) (1009802475/2147483648) (-1620366717/4294967296) 2 8 ![60,0,4] ![(27/1600),0,(1/8)] ![(1/3200),1,(1/8)] affine00557
theorem leaf00557_checked : FastNestedCellData.accepts 1 2 4 leaf00557=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (248911515403/1000000000000) (1009802475/2147483648) (-1620366717/4294967296) 2 8 ![60,0,4] ![(27/1600),0,(1/8)] ![(1/3200),1,(1/8)] 45916070216383540244142075412480000000000 26965156584523791031400092403943151239168 108332298491156083074196832256000000000000 raw00557 affine00557
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00557_raw leaf00557_rectangular
    leaf00557_transform leaf00557_sign leaf00557_log
#print axioms leaf00557_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
