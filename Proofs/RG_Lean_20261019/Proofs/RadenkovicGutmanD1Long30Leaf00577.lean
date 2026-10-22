/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00577 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 2604991806431526801464855887872000000000 1484456546392956876031216707836043067392 5606341881971091847708357427200000000000))
theorem leaf00577_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 2604991806431526801464855887872000000000 1484456546392956876031216707836043067392 5606341881971091847708357427200000000000 raw00577=true := by decide +kernel
#print axioms leaf00577_raw
theorem leaf00577_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00577=true := by decide +kernel
#print axioms leaf00577_rectangular
def affine00577 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00577 (IntegerComputedClassCell.leftNumerator ![(29/1600),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(29/1600),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(29/1600),0,(1/8)] ![(1/3200),1,(1/8)]))
theorem leaf00577_transform : affine00577=(NestedInteger.clearedAll 3 raw00577 (IntegerComputedClassCell.leftNumerator ![(29/1600),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(29/1600),0,(1/8)] ![(1/3200),1,(1/8)]) (IntegerComputedClassCell.denominator ![(29/1600),0,(1/8)] ![(1/3200),1,(1/8)])) := by decide +kernel
#print axioms leaf00577_transform
theorem leaf00577_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00577=true := by decide +kernel
#print axioms leaf00577_sign
theorem leaf00577_log : RationalLog.accepts (1935108975/4294967296) (-1712146475/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00577_log
def leaf00577 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (52956333297/200000000000) (1935108975/4294967296) (-1712146475/4294967296) 2 8 ![60,0,4] ![(29/1600),0,(1/8)] ![(1/3200),1,(1/8)] affine00577
theorem leaf00577_checked : FastNestedCellData.accepts 1 2 4 leaf00577=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (52956333297/200000000000) (1935108975/4294967296) (-1712146475/4294967296) 2 8 ![60,0,4] ![(29/1600),0,(1/8)] ![(1/3200),1,(1/8)] 2604991806431526801464855887872000000000 1484456546392956876031216707836043067392 5606341881971091847708357427200000000000 raw00577 affine00577
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00577_raw leaf00577_rectangular
    leaf00577_transform leaf00577_sign leaf00577_log
#print axioms leaf00577_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
