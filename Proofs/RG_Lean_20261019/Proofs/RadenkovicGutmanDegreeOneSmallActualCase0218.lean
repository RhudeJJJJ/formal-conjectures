/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0218 : Family 5 := level5.get ⟨5,by decide⟩
def sourceMap0218 : (Vertices 5 ⊕ Fin 3 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 5 2 3 v)
def fusedMap0218 : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 2 3 v)
theorem sourceMap0218_checked : acceptsGraphIso
    (source (graph core0218) (root 5) 2 3) DegreeOneSmallSpectrum1038.graph sourceMap0218=true := by decide +kernel
theorem fusedMap0218_checked : acceptsGraphIso
    (fused (graph core0218) (root 5) 2 3) DegreeOneSmallSpectrum870.graph fusedMap0218=true := by decide +kernel
theorem certified0218 : Certified (graph core0218) (root 5) 2 3 :=
  of_native_maps core0218 DegreeOneSmallSpectrum1038.graph DegreeOneSmallSpectrum870.graph
    sourceMap0218 fusedMap0218 sourceMap0218_checked fusedMap0218_checked
    DegreeOneSmallComparisons.comparison0218
#print axioms sourceMap0218_checked
#print axioms fusedMap0218_checked
#print axioms certified0218
def sourceMap0218swap : (Vertices 5 ⊕ Fin 4 ⊕ Fin 3) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,9,10,11,12,6,7,8] (sourceLabel 5 3 2 v)
def fusedMap0218swap : (Vertices 5 ⊕ Fin 7) → Fin 13 :=
  fun v => ![2,3,4,5,6,7,1,0,8,9,10,11,12] (fusedLabel 5 3 2 v)
theorem sourceMap0218swap_checked : acceptsGraphIso
    (source (graph core0218) (root 5) 3 2) DegreeOneSmallSpectrum1038.graph sourceMap0218swap=true := by decide +kernel
theorem fusedMap0218swap_checked : acceptsGraphIso
    (fused (graph core0218) (root 5) 3 2) DegreeOneSmallSpectrum870.graph fusedMap0218swap=true := by decide +kernel
theorem certified0218swap : Certified (graph core0218) (root 5) 3 2 :=
  of_native_maps core0218 DegreeOneSmallSpectrum1038.graph DegreeOneSmallSpectrum870.graph
    sourceMap0218swap fusedMap0218swap sourceMap0218swap_checked fusedMap0218swap_checked
    DegreeOneSmallComparisons.comparison0218
#print axioms sourceMap0218swap_checked
#print axioms fusedMap0218swap_checked
#print axioms certified0218swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
