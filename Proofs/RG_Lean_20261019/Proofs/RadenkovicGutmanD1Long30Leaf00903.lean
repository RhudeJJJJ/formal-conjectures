/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00903 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 7169734530931249688159205720064000000000000 3780979912769903091699943944490270932860928 9727942993956838091914248978432000000000000))
theorem leaf00903_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 7169734530931249688159205720064000000000000 3780979912769903091699943944490270932860928 9727942993956838091914248978432000000000000 raw00903=true := by decide +kernel
#print axioms leaf00903_raw
theorem leaf00903_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00903=true := by decide +kernel
#print axioms leaf00903_rectangular
def affine00903 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00903 (IntegerComputedClassCell.leftNumerator ![(11/160),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/160),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/160),0,(1/4)] ![(1/640),1,(1/4)]))
theorem leaf00903_transform : affine00903=(NestedInteger.clearedAll 3 raw00903 (IntegerComputedClassCell.leftNumerator ![(11/160),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/160),0,(1/4)] ![(1/640),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/160),0,(1/4)] ![(1/640),1,(1/4)])) := by decide +kernel
#print axioms leaf00903_transform
theorem leaf00903_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00903=true := by decide +kernel
#print axioms leaf00903_sign
theorem leaf00903_log : RationalLog.accepts (1631028123/4294967296) (-2079265411/4294967296) 2 8=true := by decide +kernel
#print axioms leaf00903_log
def leaf00903 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (388672087729/1000000000000) (1631028123/4294967296) (-2079265411/4294967296) 2 8 ![60,0,4] ![(11/160),0,(1/4)] ![(1/640),1,(1/4)] affine00903
theorem leaf00903_checked : FastNestedCellData.accepts 1 2 4 leaf00903=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (388672087729/1000000000000) (1631028123/4294967296) (-2079265411/4294967296) 2 8 ![60,0,4] ![(11/160),0,(1/4)] ![(1/640),1,(1/4)] 7169734530931249688159205720064000000000000 3780979912769903091699943944490270932860928 9727942993956838091914248978432000000000000 raw00903 affine00903
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00903_raw leaf00903_rectangular
    leaf00903_transform leaf00903_sign leaf00903_log
#print axioms leaf00903_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
