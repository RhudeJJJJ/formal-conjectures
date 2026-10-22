/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00079 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 19153868260928656423061028864000000000000 18822804816718802221225339675110543458304 2589700408392780217373916397568000000000000))
theorem leaf00079_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 19153868260928656423061028864000000000000 18822804816718802221225339675110543458304 2589700408392780217373916397568000000000000 raw00079=true := by decide +kernel
#print axioms leaf00079_raw
theorem leaf00079_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00079=true := by decide +kernel
#print axioms leaf00079_rectangular
def affine00079 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00079 (IntegerComputedClassCell.leftNumerator ![(31/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/16000),0,(1/2)] ![(1/16000),1,(1/2)]))
theorem leaf00079_transform : affine00079=(NestedInteger.clearedAll 3 raw00079 (IntegerComputedClassCell.leftNumerator ![(31/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(31/16000),0,(1/2)] ![(1/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(31/16000),0,(1/2)] ![(1/16000),1,(1/2)])) := by decide +kernel
#print axioms leaf00079_transform
theorem leaf00079_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00079=true := by decide +kernel
#print axioms leaf00079_sign
theorem leaf00079_log : RationalLog.accepts (4190274977/4294967296) (-52994741/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00079_log
def leaf00079 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (7268332953/1000000000000) (4190274977/4294967296) (-52994741/4294967296) 1 8 ![60,0,4] ![(31/16000),0,(1/2)] ![(1/16000),1,(1/2)] affine00079
theorem leaf00079_checked : FastNestedCellData.accepts 1 2 4 leaf00079=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (7268332953/1000000000000) (4190274977/4294967296) (-52994741/4294967296) 1 8 ![60,0,4] ![(31/16000),0,(1/2)] ![(1/16000),1,(1/2)] 19153868260928656423061028864000000000000 18822804816718802221225339675110543458304 2589700408392780217373916397568000000000000 raw00079 affine00079
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00079_raw leaf00079_rectangular
    leaf00079_transform leaf00079_sign leaf00079_log
#print axioms leaf00079_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
