/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0249 : Family 5 := level5.get ⟨9,by decide⟩
def sourceMap0249 : (Vertices 5 ⊕ Fin 2 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,5,6,7,8,9,1,2,3,4] (sourceLabel 5 1 1 v)
def fusedMap0249 : (Vertices 5 ⊕ Fin 4) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 5 1 1 v)
theorem sourceMap0249_checked : acceptsGraphIso
    (source (graph core0249) (root 5) 1 1) DegreeOneSmallSpectrum135.graph sourceMap0249=true := by decide +kernel
theorem fusedMap0249_checked : acceptsGraphIso
    (fused (graph core0249) (root 5) 1 1) DegreeOneSmallSpectrum082.graph fusedMap0249=true := by decide +kernel
theorem certified0249 : Certified (graph core0249) (root 5) 1 1 :=
  of_native_maps core0249 DegreeOneSmallSpectrum135.graph DegreeOneSmallSpectrum082.graph
    sourceMap0249 fusedMap0249 sourceMap0249_checked fusedMap0249_checked
    DegreeOneSmallComparisons.comparison0249
#print axioms sourceMap0249_checked
#print axioms fusedMap0249_checked
#print axioms certified0249
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
