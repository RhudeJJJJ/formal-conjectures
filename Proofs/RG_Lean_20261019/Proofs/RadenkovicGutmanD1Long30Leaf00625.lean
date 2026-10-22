/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm30
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00625 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![60,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm30.pack false 3907115739363302054295100194816000000000000 68804147488553027990086753466871648878592 81211601127148369098517250048000000000000))
theorem leaf00625_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm30.pack
    false 3907115739363302054295100194816000000000000 68804147488553027990086753466871648878592 81211601127148369098517250048000000000000 raw00625=true := by decide +kernel
#print axioms leaf00625_raw
theorem leaf00625_rectangular : NestedInteger.rectangular 3 ![60,0,4] raw00625=true := by decide +kernel
#print axioms leaf00625_rectangular
def affine00625 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00625 (IntegerComputedClassCell.leftNumerator ![(7/320),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/320),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/320),0,0] ![(3/6400),1,(1/16)]))
theorem leaf00625_transform : affine00625=(NestedInteger.clearedAll 3 raw00625 (IntegerComputedClassCell.leftNumerator ![(7/320),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.widthNumerator ![(7/320),0,0] ![(3/6400),1,(1/16)]) (IntegerComputedClassCell.denominator ![(7/320),0,0] ![(3/6400),1,(1/16)])) := by decide +kernel
#print axioms leaf00625_transform
theorem leaf00625_sign : NestedInteger.bernsteinCheck 3 ![60,0,4] affine00625=true := by decide +kernel
#print axioms leaf00625_sign
theorem leaf00625_log : RationalLog.accepts (40944863/4294967296) (-9992183385/4294967296) 7 8=true := by decide +kernel
#print axioms leaf00625_log
def leaf00625 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack30.pack false (423610337277/500000000000) (40944863/4294967296) (-9992183385/4294967296) 7 8 ![60,0,4] ![(7/320),0,0] ![(3/6400),1,(1/16)] affine00625
theorem leaf00625_checked : FastNestedCellData.accepts 1 2 4 leaf00625=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm30.pack false (423610337277/500000000000) (40944863/4294967296) (-9992183385/4294967296) 7 8 ![60,0,4] ![(7/320),0,0] ![(3/6400),1,(1/16)] 3907115739363302054295100194816000000000000 68804147488553027990086753466871648878592 81211601127148369098517250048000000000000 raw00625 affine00625
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00625_raw leaf00625_rectangular
    leaf00625_transform leaf00625_sign leaf00625_log
#print axioms leaf00625_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass30
