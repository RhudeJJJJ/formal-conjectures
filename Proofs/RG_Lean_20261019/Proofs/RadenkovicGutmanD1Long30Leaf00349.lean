/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00349 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 142025303557541743590566264832000000000000 132239082413667204509512690935843054944256 4293918845311226856175862546432000000000000))
theorem leaf00349_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 142025303557541743590566264832000000000000 132239082413667204509512690935843054944256 4293918845311226856175862546432000000000000 raw00349=true := by decide +kernel
#print axioms leaf00349_raw
theorem leaf00349_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00349=true := by decide +kernel
#print axioms leaf00349_rectangular
def affine00349 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00349 (IntegerComputedClassCell.leftNumerator ![(53/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(53/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(53/6400),0,(1/2)] ![(1/6400),1,(1/2)]))
theorem leaf00349_transform : affine00349=(NestedInteger.clearedAll 3 raw00349 (IntegerComputedClassCell.leftNumerator ![(53/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.widthNumerator ![(53/6400),0,(1/2)] ![(1/6400),1,(1/2)]) (IntegerComputedClassCell.denominator ![(53/6400),0,(1/2)] ![(1/6400),1,(1/2)])) := by decide +kernel
#print axioms leaf00349_transform
theorem leaf00349_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00349=true := by decide +kernel
#print axioms leaf00349_sign
theorem leaf00349_log : RationalLog.accepts (1939772923/2147483648) (-218454623/4294967296) 1 8=true := by decide +kernel
#print axioms leaf00349_log
def leaf00349 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (30796828533/1000000000000) (1939772923/2147483648) (-218454623/4294967296) 1 8 ![60,0,4] ![(53/6400),0,(1/2)] ![(1/6400),1,(1/2)] affine00349
theorem leaf00349_checked : FastNestedCellData.accepts 1 2 4 leaf00349=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (30796828533/1000000000000) (1939772923/2147483648) (-218454623/4294967296) 1 8 ![60,0,4] ![(53/6400),0,(1/2)] ![(1/6400),1,(1/2)] 142025303557541743590566264832000000000000 132239082413667204509512690935843054944256 4293918845311226856175862546432000000000000 raw00349 affine00349
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00349_raw leaf00349_rectangular
    leaf00349_transform leaf00349_sign leaf00349_log
#print axioms leaf00349_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
