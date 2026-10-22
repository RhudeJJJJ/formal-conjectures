/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00051 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 38464576026808842979118782873600000000000 34070671179657774508633714065394444009472 653581052064751812063089446092800000000000))
theorem leaf00051_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 38464576026808842979118782873600000000000 34070671179657774508633714065394444009472 653581052064751812063089446092800000000000 raw00051=true := by decide +kernel
#print axioms leaf00051_raw
theorem leaf00051_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00051=true := by decide +kernel
#print axioms leaf00051_rectangular
def affine00051 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00051 (IntegerComputedClassCell.leftNumerator ![(13/8000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/8000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/8000),0,(1/16)] ![(1/16000),1,(1/16)]))
theorem leaf00051_transform : affine00051=(NestedInteger.clearedAll 3 raw00051 (IntegerComputedClassCell.leftNumerator ![(13/8000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(13/8000),0,(1/16)] ![(1/16000),1,(1/16)]) (IntegerComputedClassCell.denominator ![(13/8000),0,(1/16)] ![(1/16000),1,(1/16)])) := by decide +kernel
#print axioms leaf00051_transform
theorem leaf00051_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00051=true := by decide +kernel
#print axioms leaf00051_sign
theorem leaf00051_log : RationalLog.accepts (3615850933/4294967296) (-369617885/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00051_log
def leaf00051 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (10425844223/200000000000) (3615850933/4294967296) (-369617885/4294967296) 1 8 ![60,0,4] ![(13/8000),0,(1/16)] ![(1/16000),1,(1/16)] affine00051
theorem leaf00051_checked : FastNestedCellData.accepts 1 2 4 leaf00051=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (10425844223/200000000000) (3615850933/4294967296) (-369617885/4294967296) 1 8 ![60,0,4] ![(13/8000),0,(1/16)] ![(1/16000),1,(1/16)] 38464576026808842979118782873600000000000 34070671179657774508633714065394444009472 653581052064751812063089446092800000000000 raw00051 affine00051
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00051_raw leaf00051_rectangular
    leaf00051_transform leaf00051_sign leaf00051_log
#print axioms leaf00051_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
