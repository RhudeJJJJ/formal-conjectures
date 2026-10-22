/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00061 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 646169434854057711902706892800000000000 567411397541785591564962990692077928448 10123982455665068005614262681600000000000))
theorem leaf00061_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 646169434854057711902706892800000000000 567411397541785591564962990692077928448 10123982455665068005614262681600000000000 raw00061=true := by decide +kernel
#print axioms leaf00061_raw
theorem leaf00061_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00061=true := by decide +kernel
#print axioms leaf00061_rectangular
def affine00061 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00061 (IntegerComputedClassCell.leftNumerator ![(7/4000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/4000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/4000),0,(1/16)] ![(1/16000),1,(1/16)]))
theorem leaf00061_transform : affine00061=(NestedInteger.clearedAll 3 raw00061 (IntegerComputedClassCell.leftNumerator ![(7/4000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/4000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/4000),0,(1/16)] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00061_transform
theorem leaf00061_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00061=true := by decide +kernel
#print axioms leaf00061_sign
theorem leaf00061_log : RationalLog.accepts (446414789/536870912) (-396230393/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00061_log
def leaf00061 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (11209252881/200000000000) (446414789/536870912) (-396230393/4294967296) 1 8 ![60,0,4] ![(7/4000),0,(1/16)] ![(1/16000),1,(1/16)] affine00061
theorem leaf00061_checked : FastNestedCellData.accepts 1 2 4 leaf00061=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (11209252881/200000000000) (446414789/536870912) (-396230393/4294967296) 1 8 ![60,0,4] ![(7/4000),0,(1/16)] ![(1/16000),1,(1/16)] 646169434854057711902706892800000000000 567411397541785591564962990692077928448 10123982455665068005614262681600000000000 raw00061 affine00061
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00061_raw leaf00061_rectangular
    leaf00061_transform leaf00061_sign leaf00061_log
#print axioms leaf00061_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
