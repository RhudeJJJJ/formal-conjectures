/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0398 : Family 6 := level6.get ⟨20,by decide⟩
def sourceMap0398 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 6 1 1 v)
def fusedMap0398 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 1 1 v)
theorem sourceMap0398_checked : acceptsGraphIso
    (source (graph core0398) (root 6) 1 1) DegreeOneSmallSpectrum256.graph sourceMap0398=true := by decide +kernel
theorem fusedMap0398_checked : acceptsGraphIso
    (fused (graph core0398) (root 6) 1 1) DegreeOneSmallSpectrum170.graph fusedMap0398=true := by decide +kernel
theorem certified0398 : Certified (graph core0398) (root 6) 1 1 :=
  of_native_maps core0398 DegreeOneSmallSpectrum256.graph DegreeOneSmallSpectrum170.graph
    sourceMap0398 fusedMap0398 sourceMap0398_checked fusedMap0398_checked
    DegreeOneSmallComparisons.comparison0398
#print axioms sourceMap0398_checked
#print axioms fusedMap0398_checked
#print axioms certified0398
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
