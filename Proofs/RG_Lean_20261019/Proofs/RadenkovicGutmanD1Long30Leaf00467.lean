/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00467 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 52581746748217479872271876096000000000000 35320927168498113557735276087492757946368 193614034401558692984994660352000000000000))
theorem leaf00467_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 52581746748217479872271876096000000000000 35320927168498113557735276087492757946368 193614034401558692984994660352000000000000 raw00467=true := by decide +kernel
#print axioms leaf00467_raw
theorem leaf00467_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00467=true := by decide +kernel
#print axioms leaf00467_rectangular
def affine00467 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00467 (IntegerComputedClassCell.leftNumerator ![(77/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(77/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(77/6400),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00467_transform : affine00467=(NestedInteger.clearedAll 3 raw00467 (IntegerComputedClassCell.leftNumerator ![(77/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(77/6400),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(77/6400),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00467_transform
theorem leaf00467_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00467=true := by decide +kernel
#print axioms leaf00467_sign
theorem leaf00467_log : RationalLog.accepts (2439954127/4294967296) (-1214326237/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00467_log
def leaf00467 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (22803697623/125000000000) (2439954127/4294967296) (-1214326237/4294967296) 1 8 ![60,0,4] ![(77/6400),0,(1/8)] ![(1/6400),1,(1/8)] affine00467
theorem leaf00467_checked : FastNestedCellData.accepts 1 2 4 leaf00467=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (22803697623/125000000000) (2439954127/4294967296) (-1214326237/4294967296) 1 8 ![60,0,4] ![(77/6400),0,(1/8)] ![(1/6400),1,(1/8)] 52581746748217479872271876096000000000000 35320927168498113557735276087492757946368 193614034401558692984994660352000000000000 raw00467 affine00467
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00467_raw leaf00467_rectangular
    leaf00467_transform leaf00467_sign leaf00467_log
#print axioms leaf00467_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
