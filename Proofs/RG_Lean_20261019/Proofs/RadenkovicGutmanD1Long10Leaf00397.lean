/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanD1IntegerNorm10
namespace Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def raw00397 : NestedInteger.Poly 3 := rg_integer_data%
  (IntegerComputedClassCell.pad 3 ![52,0,4] (IntegerNormProgramPack.polynomial DegreeOneIntegerNorm10.pack false 3626750347239847279495198277632000000000000 4825488851623602497095004168727849884188672 24543888978788981474676636123136000000000000))
theorem leaf00397_raw : IntegerNormProgramPack.rawCheck DegreeOneIntegerNorm10.pack
    false 3626750347239847279495198277632000000000000 4825488851623602497095004168727849884188672 24543888978788981474676636123136000000000000 raw00397=true := by decide +kernel
#print axioms leaf00397_raw
theorem leaf00397_rectangular : NestedInteger.rectangular 3 ![52,0,4] raw00397=true := by decide +kernel
#print axioms leaf00397_rectangular
def affine00397 : NestedInteger.Poly 3 := rg_integer_data% (NestedInteger.clearedAll 3 raw00397 (IntegerComputedClassCell.leftNumerator ![(11/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/16),0,(1/2)] ![(1/16),1,(1/4)]))
theorem leaf00397_transform : affine00397=(NestedInteger.clearedAll 3 raw00397 (IntegerComputedClassCell.leftNumerator ![(11/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.widthNumerator ![(11/16),0,(1/2)] ![(1/16),1,(1/4)]) (IntegerComputedClassCell.denominator ![(11/16),0,(1/2)] ![(1/16),1,(1/4)])) := by decide +kernel
#print axioms leaf00397_transform
theorem leaf00397_sign : NestedInteger.bernsteinCheck 3 ![52,0,4] affine00397=true := by decide +kernel
#print axioms leaf00397_sign
theorem leaf00397_log : RationalLog.accepts (4775646233/4294967296) (227816577/4294967296) 0 8=true := by decide +kernel
#print axioms leaf00397_log
def leaf00397 : FastNestedCellData.Cell := LiteralIntegerCell.make DegreeOneNormPack10.pack false (196606530277/1000000000000) (4775646233/4294967296) (227816577/4294967296) 0 8 ![52,0,4] ![(11/16),0,(1/2)] ![(1/16),1,(1/4)] affine00397
theorem leaf00397_checked : FastNestedCellData.accepts 1 0 4 leaf00397=true :=
  IntegerNormProgramPack.accepts_make DegreeOneIntegerNorm10.pack false (196606530277/1000000000000) (4775646233/4294967296) (227816577/4294967296) 0 8 ![52,0,4] ![(11/16),0,(1/2)] ![(1/16),1,(1/4)] 3626750347239847279495198277632000000000000 4825488851623602497095004168727849884188672 24543888978788981474676636123136000000000000 raw00397 affine00397
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) leaf00397_raw leaf00397_rectangular
    leaf00397_transform leaf00397_sign leaf00397_log
#print axioms leaf00397_checked
end Gebendorfer.RadenkovicGutman.DegreeOneLongClass10
