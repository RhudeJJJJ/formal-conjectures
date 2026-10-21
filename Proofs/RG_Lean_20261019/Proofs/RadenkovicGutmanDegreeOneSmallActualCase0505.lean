/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons10
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0505 : Family 7 := level7.get ⟨10,by decide⟩
def sourceMap0505 : (Vertices 7 ⊕ Fin 2 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,5,0,1,2,3,4,11,7,8,9,10] (sourceLabel 7 1 1 v)
def fusedMap0505 : (Vertices 7 ⊕ Fin 4) → Fin 12 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11] (fusedLabel 7 1 1 v)
theorem sourceMap0505_checked : acceptsGraphIso
    (source (graph core0505) (root 7) 1 1) DegreeOneSmallSpectrum482.graph sourceMap0505=true := by decide +kernel
theorem fusedMap0505_checked : acceptsGraphIso
    (fused (graph core0505) (root 7) 1 1) DegreeOneSmallSpectrum373.graph fusedMap0505=true := by decide +kernel
theorem certified0505 : Certified (graph core0505) (root 7) 1 1 :=
  of_native_maps core0505 DegreeOneSmallSpectrum482.graph DegreeOneSmallSpectrum373.graph
    sourceMap0505 fusedMap0505 sourceMap0505_checked fusedMap0505_checked
    DegreeOneSmallComparisons.comparison0505
#print axioms sourceMap0505_checked
#print axioms fusedMap0505_checked
#print axioms certified0505
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
