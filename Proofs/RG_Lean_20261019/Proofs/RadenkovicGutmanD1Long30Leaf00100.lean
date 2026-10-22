/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00100 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 4141884631650688711391241568256000000000000 346976436106336835836578652898671460352 1545331675235620544915177472000000000000))
theorem leaf00100_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 4141884631650688711391241568256000000000000 346976436106336835836578652898671460352 1545331675235620544915177472000000000000 raw00100=true := by decide +kernel
#print axioms leaf00100_raw
theorem leaf00100_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00100=true := by decide +kernel
#print axioms leaf00100_rectangular
def affine00100 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00100 (IntegerComputedClassCell.leftNumerator ![(19/8000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/8000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/8000),0,0] ![(3/32000),1,(1/16)]))
theorem leaf00100_transform : affine00100=(NestedInteger.clearedAll 3 raw00100 (IntegerComputedClassCell.leftNumerator ![(19/8000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(19/8000),0,0] ![(3/32000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(19/8000),0,0] ![(3/32000),1,(1/16)])) := by decide +kernel
#print axioms leaf00100_transform
theorem leaf00100_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00100=true := by decide +kernel
#print axioms leaf00100_sign
theorem leaf00100_log : RationalLog.accepts (293827/4294967296) (-643571561/134217728) 14 8=true := by decide +kernel
#print axioms leaf00100_log
def leaf00100 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (224532015791/1000000000000) (293827/4294967296) (-643571561/134217728) 14 8 ![60,0,4] ![(19/8000),0,0] ![(3/32000),1,(1/16)] affine00100
theorem leaf00100_checked : FastNestedCellData.accepts 1 2 4 leaf00100=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (224532015791/1000000000000) (293827/4294967296) (-643571561/134217728) 14 8 ![60,0,4] ![(19/8000),0,0] ![(3/32000),1,(1/16)] 4141884631650688711391241568256000000000000 346976436106336835836578652898671460352 1545331675235620544915177472000000000000 raw00100 affine00100
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00100_raw leaf00100_rectangular
    leaf00100_transform leaf00100_sign leaf00100_log
#print axioms leaf00100_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
