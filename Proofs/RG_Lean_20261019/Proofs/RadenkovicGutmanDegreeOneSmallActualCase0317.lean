/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0317 : Family 6 := level6.get ⟨6,by decide⟩
def sourceMap0317 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 6 1 1 v)
def fusedMap0317 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 1 1 v)
theorem sourceMap0317_checked : acceptsGraphIso
    (source (graph core0317) (root 6) 1 1) DegreeOneSmallSpectrum263.graph sourceMap0317=true := by decide +kernel
theorem fusedMap0317_checked : acceptsGraphIso
    (fused (graph core0317) (root 6) 1 1) DegreeOneSmallSpectrum175.graph fusedMap0317=true := by decide +kernel
theorem certified0317 : Certified (graph core0317) (root 6) 1 1 :=
  of_native_maps core0317 DegreeOneSmallSpectrum263.graph DegreeOneSmallSpectrum175.graph
    sourceMap0317 fusedMap0317 sourceMap0317_checked fusedMap0317_checked
    DegreeOneSmallComparisons.comparison0317
#print axioms sourceMap0317_checked
#print axioms fusedMap0317_checked
#print axioms certified0317
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
