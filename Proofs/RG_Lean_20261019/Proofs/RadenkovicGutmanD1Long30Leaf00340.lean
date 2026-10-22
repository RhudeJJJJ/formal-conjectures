/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00340 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 11066023971963963465274012729344000000000000 22163854192917903670716560695105230471168 36946508250804859254134013952000000000000))
theorem leaf00340_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 11066023971963963465274012729344000000000000 22163854192917903670716560695105230471168 36946508250804859254134013952000000000000 raw00340=true := by decide +kernel
#print axioms leaf00340_raw
theorem leaf00340_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00340=true := by decide +kernel
#print axioms leaf00340_rectangular
def affine00340 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00340 (IntegerComputedClassCell.leftNumerator ![(13/1600),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/1600),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/1600),0,0] ![(1/6400),1,(1/16)]))
theorem leaf00340_transform : affine00340=(NestedInteger.clearedAll 3 raw00340 (IntegerComputedClassCell.leftNumerator ![(13/1600),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/1600),0,0] ![(1/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/1600),0,0] ![(1/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00340_transform
theorem leaf00340_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00340=true := by decide +kernel
#print axioms leaf00340_sign
theorem leaf00340_log : RationalLog.accepts (5376793/4294967296) (-14351863611/4294967296) 10 8=true := by decide +kernel
#print axioms leaf00340_log
def leaf00340 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (599890361559/1000000000000) (5376793/4294967296) (-14351863611/4294967296) 10 8 ![60,0,4] ![(13/1600),0,0] ![(1/6400),1,(1/16)] affine00340
theorem leaf00340_checked : FastNestedCellData.accepts 1 2 4 leaf00340=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (599890361559/1000000000000) (5376793/4294967296) (-14351863611/4294967296) 10 8 ![60,0,4] ![(13/1600),0,0] ![(1/6400),1,(1/16)] 11066023971963963465274012729344000000000000 22163854192917903670716560695105230471168 36946508250804859254134013952000000000000 raw00340 affine00340
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00340_raw leaf00340_rectangular
    leaf00340_transform leaf00340_sign leaf00340_log
#print axioms leaf00340_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
