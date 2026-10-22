/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00620 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 973677967887593412140118048768000000000000 16397999211313076372798413351515920007168 19416692732880576217429835776000000000000))
theorem leaf00620_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 973677967887593412140118048768000000000000 16397999211313076372798413351515920007168 19416692732880576217429835776000000000000 raw00620=true := by decide +kernel
#print axioms leaf00620_raw
theorem leaf00620_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00620=true := by decide +kernel
#print axioms leaf00620_rectangular
def affine00620 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00620 (IntegerComputedClassCell.leftNumerator ![(137/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(137/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(137/6400),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00620_transform : affine00620=(NestedInteger.clearedAll 3 raw00620 (IntegerComputedClassCell.leftNumerator ![(137/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(137/6400),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(137/6400),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00620_transform
theorem leaf00620_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00620=true := by decide +kernel
#print axioms leaf00620_sign
theorem leaf00620_log : RationalLog.accepts (39214747/4294967296) (-2521224433/1073741824) 7 8=true := by decide +kernel
#print axioms leaf00620_log
def leaf00620 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (211132753617/250000000000) (39214747/4294967296) (-2521224433/1073741824) 7 8 ![60,0,4] ![(137/6400),0,0] ![(3/6400),1,(1/16)] affine00620
theorem leaf00620_checked : FastNestedCellData.accepts 1 2 4 leaf00620=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (211132753617/250000000000) (39214747/4294967296) (-2521224433/1073741824) 7 8 ![60,0,4] ![(137/6400),0,0] ![(3/6400),1,(1/16)] 973677967887593412140118048768000000000000 16397999211313076372798413351515920007168 19416692732880576217429835776000000000000 raw00620 affine00620
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00620_raw leaf00620_rectangular
    leaf00620_transform leaf00620_sign leaf00620_log
#print axioms leaf00620_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
