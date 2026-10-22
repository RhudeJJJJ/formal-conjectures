/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0428 : Family 10 := level10.get ⟨150,by decide⟩
def sourceMap0428 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0428 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0428_checked : acceptsGraphIso
    (source (graph core0428) (root 10) 0 0) DegreeOneSmallSpectrum1081.graph sourceMap0428=true := by decide +kernel
theorem fusedMap0428_checked : acceptsGraphIso
    (fused (graph core0428) (root 10) 0 0) DegreeOneSmallSpectrum941.graph fusedMap0428=true := by decide +kernel
theorem certified0428 : Certified (graph core0428) (root 10) 0 0 :=
  of_native_maps core0428 DegreeOneSmallSpectrum1081.graph DegreeOneSmallSpectrum941.graph
    sourceMap0428 fusedMap0428 sourceMap0428_checked fusedMap0428_checked
    DegreeTwoThreeFiniteComparisons.comparison0428
#print axioms sourceMap0428_checked
#print axioms fusedMap0428_checked
#print axioms certified0428
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
