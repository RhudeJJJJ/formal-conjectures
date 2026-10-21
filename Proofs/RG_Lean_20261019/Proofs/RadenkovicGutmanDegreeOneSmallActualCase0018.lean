/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons00
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0018 : Family 1 := level1.get ⟨0,by decide⟩
def sourceMap0018 : (Vertices 1 ⊕ Fin 3 ⊕ Fin 3) → Fin 8 :=
  fun v => ![0,7,1,2,3,4,5,6] (sourceLabel 1 2 2 v)
def fusedMap0018 : (Vertices 1 ⊕ Fin 6) → Fin 8 :=
  fun v => ![2,3,1,0,4,5,6,7] (fusedLabel 1 2 2 v)
theorem sourceMap0018_checked : acceptsGraphIso
    (source (graph core0018) (root 1) 2 2) DegreeOneSmallSpectrum026.graph sourceMap0018=true := by decide +kernel
theorem fusedMap0018_checked : acceptsGraphIso
    (fused (graph core0018) (root 1) 2 2) DegreeOneSmallSpectrum016.graph fusedMap0018=true := by decide +kernel
theorem certified0018 : Certified (graph core0018) (root 1) 2 2 :=
  of_native_maps core0018 DegreeOneSmallSpectrum026.graph DegreeOneSmallSpectrum016.graph
    sourceMap0018 fusedMap0018 sourceMap0018_checked fusedMap0018_checked
    DegreeOneSmallComparisons.comparison0018
#print axioms sourceMap0018_checked
#print axioms fusedMap0018_checked
#print axioms certified0018
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
