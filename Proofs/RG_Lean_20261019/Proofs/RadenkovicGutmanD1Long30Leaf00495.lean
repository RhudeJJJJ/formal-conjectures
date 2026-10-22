/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00495 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 865077669273476566884145954816000000000000 5158146479044578225515976425911512727552 6874455567205934540963971072000000000000))
theorem leaf00495_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 865077669273476566884145954816000000000000 5158146479044578225515976425911512727552 6874455567205934540963971072000000000000 raw00495=true := by decide +kernel
#print axioms leaf00495_raw
theorem leaf00495_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00495=true := by decide +kernel
#print axioms leaf00495_rectangular
def affine00495 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00495 (IntegerComputedClassCell.leftNumerator ![(21/1600),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/1600),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/1600),0,0] ![(1/3200),1,(1/16)]))
theorem leaf00495_transform : affine00495=(NestedInteger.clearedAll 3 raw00495 (IntegerComputedClassCell.leftNumerator ![(21/1600),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(21/1600),0,0] ![(1/3200),1,(1/16)]) (IntegerComputedClassCell.denominator ![(21/1600),0,0] ![(1/3200),1,(1/16)])) := by decide +kernel
#print axioms leaf00495_transform
theorem leaf00495_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00495=true := by decide +kernel
#print axioms leaf00495_sign
theorem leaf00495_log : RationalLog.accepts (14631107/4294967296) (-12202108365/4294967296) 9 8=true := by decide +kernel
#print axioms leaf00495_log
def leaf00495 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (187583817679/250000000000) (14631107/4294967296) (-12202108365/4294967296) 9 8 ![60,0,4] ![(21/1600),0,0] ![(1/3200),1,(1/16)] affine00495
theorem leaf00495_checked : FastNestedCellData.accepts 1 2 4 leaf00495=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (187583817679/250000000000) (14631107/4294967296) (-12202108365/4294967296) 9 8 ![60,0,4] ![(21/1600),0,0] ![(1/3200),1,(1/16)] 865077669273476566884145954816000000000000 5158146479044578225515976425911512727552 6874455567205934540963971072000000000000 raw00495 affine00495
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00495_raw leaf00495_rectangular
    leaf00495_transform leaf00495_sign leaf00495_log
#print axioms leaf00495_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
