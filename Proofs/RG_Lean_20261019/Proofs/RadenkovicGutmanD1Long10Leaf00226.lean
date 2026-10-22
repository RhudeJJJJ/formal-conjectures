/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00226 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 320832865252260554726791184384000000000000 186221989992828053296921861290353674420224 669193714691920175398687604736000000000000))
theorem leaf00226_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 320832865252260554726791184384000000000000 186221989992828053296921861290353674420224 669193714691920175398687604736000000000000 raw00226=true := by decide +kernel
#print axioms leaf00226_raw
theorem leaf00226_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00226=true := by decide +kernel
#print axioms leaf00226_rectangular
def affine00226 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00226 (IntegerComputedClassCell.leftNumerator ![(13/320),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/320),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/320),0,(1/4)] ![(3/3200),1,(1/4)]))
theorem leaf00226_transform : affine00226=(NestedInteger.clearedAll 3 raw00226 (IntegerComputedClassCell.leftNumerator ![(13/320),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/320),0,(1/4)] ![(3/3200),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/320),0,(1/4)] ![(3/3200),1,(1/4)])) := by decide +kernel
#print axioms leaf00226_transform
theorem leaf00226_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00226=true := by decide +kernel
#print axioms leaf00226_sign
theorem leaf00226_log : RationalLog.accepts (487558371/1073741824) (-1695427331/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00226_log
def leaf00226 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (278278151609/1000000000000) (487558371/1073741824) (-1695427331/4294967296) 2 8 ![52,0,4] ![(13/320),0,(1/4)] ![(3/3200),1,(1/4)] affine00226
theorem leaf00226_checked : FastNestedCellData.accepts 1 0 4 leaf00226=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (278278151609/1000000000000) (487558371/1073741824) (-1695427331/4294967296) 2 8 ![52,0,4] ![(13/320),0,(1/4)] ![(3/3200),1,(1/4)] 320832865252260554726791184384000000000000 186221989992828053296921861290353674420224 669193714691920175398687604736000000000000 raw00226 affine00226
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00226_raw leaf00226_rectangular
    leaf00226_transform leaf00226_sign leaf00226_log
#print axioms leaf00226_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
