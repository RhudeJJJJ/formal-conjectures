/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00348 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2907597845947082601382367199232000000000000 1440289773016357721567819829584634553827328 2284416401656798582735598780416000000000000))
theorem leaf00348_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2907597845947082601382367199232000000000000 1440289773016357721567819829584634553827328 2284416401656798582735598780416000000000000 raw00348=true := by decide +kernel
#print axioms leaf00348_raw
theorem leaf00348_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00348=true := by decide +kernel
#print axioms leaf00348_rectangular
def affine00348 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00348 (IntegerComputedClassCell.leftNumerator ![(13/80),0,0] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/80),0,0] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/80),0,0] ![(1/80),1,(1/4)]))
theorem leaf00348_transform : affine00348=(NestedInteger.clearedAll 3 raw00348 (IntegerComputedClassCell.leftNumerator ![(13/80),0,0] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(13/80),0,0] ![(1/80),1,(1/4)]) (IntegerComputedClassCell.denominator ![(13/80),0,0] ![(1/80),1,(1/4)])) := by decide +kernel
#print axioms leaf00348_transform
theorem leaf00348_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00348=true := by decide +kernel
#print axioms leaf00348_sign
theorem leaf00348_log : RationalLog.accepts (1304844173/4294967296) (-1279213433/2147483648) 2 8=true := by decide +kernel
#print axioms leaf00348_log
def leaf00348 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (315242390129/500000000000) (1304844173/4294967296) (-1279213433/2147483648) 2 8 ![52,0,4] ![(13/80),0,0] ![(1/80),1,(1/4)] affine00348
theorem leaf00348_checked : FastNestedCellData.accepts 1 0 4 leaf00348=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (315242390129/500000000000) (1304844173/4294967296) (-1279213433/2147483648) 2 8 ![52,0,4] ![(13/80),0,0] ![(1/80),1,(1/4)] 2907597845947082601382367199232000000000000 1440289773016357721567819829584634553827328 2284416401656798582735598780416000000000000 raw00348 affine00348
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00348_raw leaf00348_rectangular
    leaf00348_transform leaf00348_sign leaf00348_log
#print axioms leaf00348_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
