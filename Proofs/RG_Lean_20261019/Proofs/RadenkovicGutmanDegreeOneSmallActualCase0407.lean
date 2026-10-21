/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0407 : Family 6 := level6.get ⟨22,by decide⟩
def sourceMap0407 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (sourceLabel 6 1 1 v)
def fusedMap0407 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 1 1 v)
theorem sourceMap0407_checked : acceptsGraphIso
    (source (graph core0407) (root 6) 1 1) DegreeOneSmallSpectrum278.graph sourceMap0407=true := by decide +kernel
theorem fusedMap0407_checked : acceptsGraphIso
    (fused (graph core0407) (root 6) 1 1) DegreeOneSmallSpectrum176.graph fusedMap0407=true := by decide +kernel
theorem certified0407 : Certified (graph core0407) (root 6) 1 1 :=
  of_native_maps core0407 DegreeOneSmallSpectrum278.graph DegreeOneSmallSpectrum176.graph
    sourceMap0407 fusedMap0407 sourceMap0407_checked fusedMap0407_checked
    DegreeOneSmallComparisons.comparison0407
#print axioms sourceMap0407_checked
#print axioms fusedMap0407_checked
#print axioms certified0407
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
