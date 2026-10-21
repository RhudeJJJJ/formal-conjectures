/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0392 : Family 6 := level6.get ⟨19,by decide⟩
def sourceMap0392 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 2 2 v)
def fusedMap0392 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap0392_checked : acceptsGraphIso
    (source (graph core0392) (root 6) 2 2) DegreeOneSmallSpectrum1597.graph sourceMap0392=true := by decide +kernel
theorem fusedMap0392_checked : acceptsGraphIso
    (fused (graph core0392) (root 6) 2 2) DegreeOneSmallSpectrum862.graph fusedMap0392=true := by decide +kernel
theorem certified0392 : Certified (graph core0392) (root 6) 2 2 :=
  of_native_maps core0392 DegreeOneSmallSpectrum1597.graph DegreeOneSmallSpectrum862.graph
    sourceMap0392 fusedMap0392 sourceMap0392_checked fusedMap0392_checked
    DegreeOneSmallComparisons.comparison0392
#print axioms sourceMap0392_checked
#print axioms fusedMap0392_checked
#print axioms certified0392
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
