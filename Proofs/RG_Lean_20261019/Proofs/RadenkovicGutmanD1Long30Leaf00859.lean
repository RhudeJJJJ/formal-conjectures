/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00859 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 861505831189881714269464035328000000000000 605166316082006230278014955980336222175232 3239487113910756653277355442176000000000000))
theorem leaf00859_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 861505831189881714269464035328000000000000 605166316082006230278014955980336222175232 3239487113910756653277355442176000000000000 raw00859=true := by decide +kernel
#print axioms leaf00859_raw
theorem leaf00859_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00859=true := by decide +kernel
#print axioms leaf00859_rectangular
def affine00859 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00859 (IntegerComputedClassCell.leftNumerator ![(7/128),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/128),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/128),0,(1/2)] ![(1/640),1,(1/2)]))
theorem leaf00859_transform : affine00859=(NestedInteger.clearedAll 3 raw00859 (IntegerComputedClassCell.leftNumerator ![(7/128),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/128),0,(1/2)] ![(1/640),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/128),0,(1/2)] ![(1/640),1,(1/2)])) := by decide +kernel
#print axioms leaf00859_transform
theorem leaf00859_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00859=true := by decide +kernel
#print axioms leaf00859_sign
theorem leaf00859_log : RationalLog.accepts (1271058241/2147483648) (-1126241277/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00859_log
def leaf00859 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (186809298757/1000000000000) (1271058241/2147483648) (-1126241277/4294967296) 1 8 ![60,0,4] ![(7/128),0,(1/2)] ![(1/640),1,(1/2)] affine00859
theorem leaf00859_checked : FastNestedCellData.accepts 1 2 4 leaf00859=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (186809298757/1000000000000) (1271058241/2147483648) (-1126241277/4294967296) 1 8 ![60,0,4] ![(7/128),0,(1/2)] ![(1/640),1,(1/2)] 861505831189881714269464035328000000000000 605166316082006230278014955980336222175232 3239487113910756653277355442176000000000000 raw00859 affine00859
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00859_raw leaf00859_rectangular
    leaf00859_transform leaf00859_sign leaf00859_log
#print axioms leaf00859_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
