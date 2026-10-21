/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0428 : Family 6 := level6.get ⟨27,by decide⟩
def sourceMap0428 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 2 2 v)
def fusedMap0428 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap0428_checked : acceptsGraphIso
    (source (graph core0428) (root 6) 2 2) DegreeOneSmallSpectrum1911.graph sourceMap0428=true := by decide +kernel
theorem fusedMap0428_checked : acceptsGraphIso
    (fused (graph core0428) (root 6) 2 2) DegreeOneSmallSpectrum909.graph fusedMap0428=true := by decide +kernel
theorem certified0428 : Certified (graph core0428) (root 6) 2 2 :=
  of_native_maps core0428 DegreeOneSmallSpectrum1911.graph DegreeOneSmallSpectrum909.graph
    sourceMap0428 fusedMap0428 sourceMap0428_checked fusedMap0428_checked
    DegreeOneSmallComparisons.comparison0428
#print axioms sourceMap0428_checked
#print axioms fusedMap0428_checked
#print axioms certified0428
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
