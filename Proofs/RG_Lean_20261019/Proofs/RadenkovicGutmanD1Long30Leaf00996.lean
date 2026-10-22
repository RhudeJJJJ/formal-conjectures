/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00996 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 11613650439266525668538782318592000000000000 6260722192781397056634751436470095836086272 9944327204506941732655523168256000000000000))
theorem leaf00996_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 11613650439266525668538782318592000000000000 6260722192781397056634751436470095836086272 9944327204506941732655523168256000000000000 raw00996=true := by decide +kernel
#print axioms leaf00996_raw
theorem leaf00996_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00996=true := by decide +kernel
#print axioms leaf00996_rectangular
def affine00996 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00996 (IntegerComputedClassCell.leftNumerator ![(23/160),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/160),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/160),0,(1/16)] ![(1/160),1,(1/16)]))
theorem leaf00996_transform : affine00996=(NestedInteger.clearedAll 3 raw00996 (IntegerComputedClassCell.leftNumerator ![(23/160),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(23/160),0,(1/16)] ![(1/160),1,(1/16)]) (IntegerComputedClassCell.denominator ![(23/160),0,(1/16)] ![(1/160),1,(1/16)])) := by decide +kernel
#print axioms leaf00996_transform
theorem leaf00996_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00996=true := by decide +kernel
#print axioms leaf00996_sign
theorem leaf00996_log : RationalLog.accepts (1420825003/4294967296) (-74236247/134217728) 2 8=true := by decide +kernel
#print axioms leaf00996_log
def leaf00996 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (629577251837/1000000000000) (1420825003/4294967296) (-74236247/134217728) 2 8 ![60,0,4] ![(23/160),0,(1/16)] ![(1/160),1,(1/16)] affine00996
theorem leaf00996_checked : FastNestedCellData.accepts 1 2 4 leaf00996=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (629577251837/1000000000000) (1420825003/4294967296) (-74236247/134217728) 2 8 ![60,0,4] ![(23/160),0,(1/16)] ![(1/160),1,(1/16)] 11613650439266525668538782318592000000000000 6260722192781397056634751436470095836086272 9944327204506941732655523168256000000000000 raw00996 affine00996
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00996_raw leaf00996_rectangular
    leaf00996_transform leaf00996_sign leaf00996_log
#print axioms leaf00996_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
