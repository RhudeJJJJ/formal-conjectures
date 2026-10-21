/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0547 : Family 7 := level7.get ⟨19,by decide⟩
def sourceMap0547 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![1,0,7,8,9,10,11,6,2,3,4,5] (sourceLabel 7 1 1 v)
def fusedMap0547 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0547_checked : acceptsGraphIso
    (source (graph core0547) (root 7) 1 1) DegreeOneSmallSpectrum509.graph sourceMap0547=true := by decide +kernel
theorem fusedMap0547_checked : acceptsGraphIso
    (fused (graph core0547) (root 7) 1 1) DegreeOneSmallSpectrum389.graph fusedMap0547=true := by decide +kernel
theorem certified0547 : Certified (graph core0547) (root 7) 1 1 :=
  of_native_maps core0547 DegreeOneSmallSpectrum509.graph DegreeOneSmallSpectrum389.graph
    sourceMap0547 fusedMap0547 sourceMap0547_checked fusedMap0547_checked
    DegreeOneSmallComparisons.comparison0547
#print axioms sourceMap0547_checked
#print axioms fusedMap0547_checked
#print axioms certified0547
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
