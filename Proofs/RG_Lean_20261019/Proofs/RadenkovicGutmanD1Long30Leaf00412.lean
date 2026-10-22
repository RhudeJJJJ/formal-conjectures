/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00412 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 9707131327612895336416359219200000000000 6855449407464602351235308150886512984064 43425366520671004138020431462400000000000))
theorem leaf00412_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 9707131327612895336416359219200000000000 6855449407464602351235308150886512984064 43425366520671004138020431462400000000000 raw00412=true := by decide +kernel
#print axioms leaf00412_raw
theorem leaf00412_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00412=true := by decide +kernel
#print axioms leaf00412_rectangular
def affine00412 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00412 (IntegerComputedClassCell.leftNumerator ![(33/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(33/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(33/3200),0,(1/8)] ![(1/6400),1,(1/8)]))
theorem leaf00412_transform : affine00412=(NestedInteger.clearedAll 3 raw00412 (IntegerComputedClassCell.leftNumerator ![(33/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.widthNumerator ![(33/3200),0,(1/8)] ![(1/6400),1,(1/8)]) (IntegerComputedClassCell.denominator ![(33/3200),0,(1/8)] ![(1/6400),1,(1/8)])) := by decide +kernel
#print axioms leaf00412_transform
theorem leaf00412_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00412=true := by decide +kernel
#print axioms leaf00412_sign
theorem leaf00412_log : RationalLog.accepts (2619666837/4294967296) (-132713633/536870912) 1 8=true := by decide +kernel
#print axioms leaf00412_log
def leaf00412 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (15786739311/100000000000) (2619666837/4294967296) (-132713633/536870912) 1 8 ![60,0,4] ![(33/3200),0,(1/8)] ![(1/6400),1,(1/8)] affine00412
theorem leaf00412_checked : FastNestedCellData.accepts 1 2 4 leaf00412=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (15786739311/100000000000) (2619666837/4294967296) (-132713633/536870912) 1 8 ![60,0,4] ![(33/3200),0,(1/8)] ![(1/6400),1,(1/8)] 9707131327612895336416359219200000000000 6855449407464602351235308150886512984064 43425366520671004138020431462400000000000 raw00412 affine00412
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00412_raw leaf00412_rectangular
    leaf00412_transform leaf00412_sign leaf00412_log
#print axioms leaf00412_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
