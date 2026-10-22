/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00017 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 2390666709669551106766667776000000000000 2340644085130809767513918368235302944768 282199405866903540917801582592000000000000))
theorem leaf00017_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 2390666709669551106766667776000000000000 2340644085130809767513918368235302944768 282199405866903540917801582592000000000000 raw00017=true := by decide +kernel
#print axioms leaf00017_raw
theorem leaf00017_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00017=true := by decide +kernel
#print axioms leaf00017_rectangular
def affine00017 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00017 (IntegerComputedClassCell.leftNumerator ![(7/3200),0,(1/2)] ![(3/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/3200),0,(1/2)] ![(3/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/3200),0,(1/2)] ![(3/16000),1,(1/2)]))
theorem leaf00017_transform : affine00017=(NestedInteger.clearedAll 3 raw00017 (IntegerComputedClassCell.leftNumerator ![(7/3200),0,(1/2)] ![(3/16000),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(7/3200),0,(1/2)] ![(3/16000),1,(1/2)]) (IntegerComputedClassCell.denominator ![(7/3200),0,(1/2)] ![(3/16000),1,(1/2)])) := by decide +kernel
#print axioms leaf00017_transform
theorem leaf00017_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00017=true := by decide +kernel
#print axioms leaf00017_sign
theorem leaf00017_log : RationalLog.accepts (521313429/536870912) (-63149427/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00017_log
def leaf00017 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (8294291329/1000000000000) (521313429/536870912) (-63149427/4294967296) 1 8 ![52,0,4] ![(7/3200),0,(1/2)] ![(3/16000),1,(1/2)] affine00017
theorem leaf00017_checked : FastNestedCellData.accepts 1 0 4 leaf00017=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (8294291329/1000000000000) (521313429/536870912) (-63149427/4294967296) 1 8 ![52,0,4] ![(7/3200),0,(1/2)] ![(3/16000),1,(1/2)] 2390666709669551106766667776000000000000 2340644085130809767513918368235302944768 282199405866903540917801582592000000000000 raw00017 affine00017
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00017_raw leaf00017_rectangular
    leaf00017_transform leaf00017_sign leaf00017_log
#print axioms leaf00017_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
