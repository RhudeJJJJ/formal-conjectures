/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00372 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 1982991048119067089953317978112000000000000 1907621721964786662645310195450427088044032 4436405515787862848300640108544000000000000))
theorem leaf00372_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 1982991048119067089953317978112000000000000 1907621721964786662645310195450427088044032 4436405515787862848300640108544000000000000 raw00372=true := by decide +kernel
#print axioms leaf00372_raw
theorem leaf00372_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00372=true := by decide +kernel
#print axioms leaf00372_rectangular
def affine00372 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00372 (IntegerComputedClassCell.leftNumerator ![(5/16),0,0] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,0] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/16),0,0] ![(3/80),1,(1/4)]))
theorem leaf00372_transform : affine00372=(NestedInteger.clearedAll 3 raw00372 (IntegerComputedClassCell.leftNumerator ![(5/16),0,0] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(5/16),0,0] ![(3/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(5/16),0,0] ![(3/80),1,(1/4)])) := by decide +kernel
#print axioms leaf00372_transform
theorem leaf00372_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00372=true := by decide +kernel
#print axioms leaf00372_sign
theorem leaf00372_log : RationalLog.accepts (2889332777/4294967296) (-851301935/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00372_log
def leaf00372 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (214996320239/500000000000) (2889332777/4294967296) (-851301935/4294967296) 1 8 ![52,0,4] ![(5/16),0,0] ![(3/80),1,(1/4)] affine00372
theorem leaf00372_checked : FastNestedCellData.accepts 1 0 4 leaf00372=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (214996320239/500000000000) (2889332777/4294967296) (-851301935/4294967296) 1 8 ![52,0,4] ![(5/16),0,0] ![(3/80),1,(1/4)] 1982991048119067089953317978112000000000000 1907621721964786662645310195450427088044032 4436405515787862848300640108544000000000000 raw00372 affine00372
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00372_raw leaf00372_rectangular
    leaf00372_transform leaf00372_sign leaf00372_log
#print axioms leaf00372_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
