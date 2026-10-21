/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0394 : Family 6 := level6.get ⟨20,by decide⟩
def sourceMap0394 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (sourceLabel 6 0 1 v)
def fusedMap0394 : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 6 0 1 v)
theorem sourceMap0394_checked : acceptsGraphIso
    (source (graph core0394) (root 6) 0 1) DegreeOneSmallSpectrum100.graph sourceMap0394=true := by decide +kernel
theorem fusedMap0394_checked : acceptsGraphIso
    (fused (graph core0394) (root 6) 0 1) DegreeOneSmallSpectrum101.graph fusedMap0394=true := by decide +kernel
theorem certified0394 : Certified (graph core0394) (root 6) 0 1 :=
  of_native_maps core0394 DegreeOneSmallSpectrum100.graph DegreeOneSmallSpectrum101.graph
    sourceMap0394 fusedMap0394 sourceMap0394_checked fusedMap0394_checked
    DegreeOneSmallComparisons.comparison0394
#print axioms sourceMap0394_checked
#print axioms fusedMap0394_checked
#print axioms certified0394
def sourceMap0394swap : (Vertices 6 ⊕ Fin 2 ⊕ Fin 1) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (sourceLabel 6 1 0 v)
def fusedMap0394swap : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 6 1 0 v)
theorem sourceMap0394swap_checked : acceptsGraphIso
    (source (graph core0394) (root 6) 1 0) DegreeOneSmallSpectrum100.graph sourceMap0394swap=true := by decide +kernel
theorem fusedMap0394swap_checked : acceptsGraphIso
    (fused (graph core0394) (root 6) 1 0) DegreeOneSmallSpectrum101.graph fusedMap0394swap=true := by decide +kernel
theorem certified0394swap : Certified (graph core0394) (root 6) 1 0 :=
  of_native_maps core0394 DegreeOneSmallSpectrum100.graph DegreeOneSmallSpectrum101.graph
    sourceMap0394swap fusedMap0394swap sourceMap0394swap_checked fusedMap0394swap_checked
    DegreeOneSmallComparisons.comparison0394
#print axioms sourceMap0394swap_checked
#print axioms fusedMap0394swap_checked
#print axioms certified0394swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
