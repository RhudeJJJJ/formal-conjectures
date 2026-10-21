/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0437 : Family 6 := level6.get ⟨29,by decide⟩
def sourceMap0437 : (Vertices 6 ⊕ Fin 3 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 6 2 2 v)
def fusedMap0437 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![1,2,3,4,5,6,7,0,8,9,10,11,12] (fusedLabel 6 2 2 v)
theorem sourceMap0437_checked : acceptsGraphIso
    (source (graph core0437) (root 6) 2 2) DegreeOneSmallSpectrum1942.graph sourceMap0437=true := by decide +kernel
theorem fusedMap0437_checked : acceptsGraphIso
    (fused (graph core0437) (root 6) 2 2) DegreeOneSmallSpectrum916.graph fusedMap0437=true := by decide +kernel
theorem certified0437 : Certified (graph core0437) (root 6) 2 2 :=
  of_native_maps core0437 DegreeOneSmallSpectrum1942.graph DegreeOneSmallSpectrum916.graph
    sourceMap0437 fusedMap0437 sourceMap0437_checked fusedMap0437_checked
    DegreeOneSmallComparisons.comparison0437
#print axioms sourceMap0437_checked
#print axioms fusedMap0437_checked
#print axioms certified0437
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
