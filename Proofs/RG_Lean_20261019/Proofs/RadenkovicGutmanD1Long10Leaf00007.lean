/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00007 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 18928522803042418411528257536000000000000 18315641834705511257819704968178298781696 1487455206207969802980895490048000000000000))
theorem leaf00007_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 18928522803042418411528257536000000000000 18315641834705511257819704968178298781696 1487455206207969802980895490048000000000000 raw00007=true := by decide +kernel
#print axioms leaf00007_raw
theorem leaf00007_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00007=true := by decide +kernel
#print axioms leaf00007_rectangular
def affine00007 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00007 (IntegerComputedClassCell.leftNumerator ![(3/2000),0,(1/4)] ![(1/4000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/2000),0,(1/4)] ![(1/4000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/2000),0,(1/4)] ![(1/4000),1,(1/4)]))
theorem leaf00007_transform : affine00007=(NestedInteger.clearedAll 3 raw00007 (IntegerComputedClassCell.leftNumerator ![(3/2000),0,(1/4)] ![(1/4000),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(3/2000),0,(1/4)] ![(1/4000),1,(1/4)]) (IntegerComputedClassCell.denominator ![(3/2000),0,(1/4)] ![(1/4000),1,(1/4)])) := by decide +kernel
#print axioms leaf00007_transform
theorem leaf00007_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00007=true := by decide +kernel
#print axioms leaf00007_sign
theorem leaf00007_log : RationalLog.accepts (2052675489/2147483648) (-96964725/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00007_log
def leaf00007 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (12313407327/1000000000000) (2052675489/2147483648) (-96964725/4294967296) 1 8 ![52,0,4] ![(3/2000),0,(1/4)] ![(1/4000),1,(1/4)] affine00007
theorem leaf00007_checked : FastNestedCellData.accepts 1 0 4 leaf00007=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (12313407327/1000000000000) (2052675489/2147483648) (-96964725/4294967296) 1 8 ![52,0,4] ![(3/2000),0,(1/4)] ![(1/4000),1,(1/4)] 18928522803042418411528257536000000000000 18315641834705511257819704968178298781696 1487455206207969802980895490048000000000000 raw00007 affine00007
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00007_raw leaf00007_rectangular
    leaf00007_transform leaf00007_sign leaf00007_log
#print axioms leaf00007_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
