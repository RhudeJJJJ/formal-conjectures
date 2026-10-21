/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0242 : Family 5 := level5.get ⟨8,by decide⟩
def sourceMap0242 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 5 2 3 v)
def fusedMap0242 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 2 3 v)
theorem sourceMap0242_checked : acceptsGraphIso
    (source (graph core0242) (root 5) 2 3) DegreeOneSmallSpectrum1314.graph sourceMap0242=true := by decide +kernel
theorem fusedMap0242_checked : acceptsGraphIso
    (fused (graph core0242) (root 5) 2 3) DegreeOneSmallSpectrum915.graph fusedMap0242=true := by decide +kernel
theorem certified0242 : Certified (graph core0242) (root 5) 2 3 :=
  of_native_maps core0242 DegreeOneSmallSpectrum1314.graph DegreeOneSmallSpectrum915.graph
    sourceMap0242 fusedMap0242 sourceMap0242_checked fusedMap0242_checked
    DegreeOneSmallComparisons.comparison0242
#print axioms sourceMap0242_checked
#print axioms fusedMap0242_checked
#print axioms certified0242
def sourceMap0242swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,6,7,8] (sourceLabel 5 3 2 v)
def fusedMap0242swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 3 2 v)
theorem sourceMap0242swap_checked : acceptsGraphIso
    (source (graph core0242) (root 5) 3 2) DegreeOneSmallSpectrum1314.graph sourceMap0242swap=true := by decide +kernel
theorem fusedMap0242swap_checked : acceptsGraphIso
    (fused (graph core0242) (root 5) 3 2) DegreeOneSmallSpectrum915.graph fusedMap0242swap=true := by decide +kernel
theorem certified0242swap : Certified (graph core0242) (root 5) 3 2 :=
  of_native_maps core0242 DegreeOneSmallSpectrum1314.graph DegreeOneSmallSpectrum915.graph
    sourceMap0242swap fusedMap0242swap sourceMap0242swap_checked fusedMap0242swap_checked
    DegreeOneSmallComparisons.comparison0242
#print axioms sourceMap0242swap_checked
#print axioms fusedMap0242swap_checked
#print axioms certified0242swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
