/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1155 : Family 8 := level8.get ⟨197,by decide⟩
def sourceMap1155 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,8,9,10,6,7] (sourceLabel 8 0 0 v)
def fusedMap1155 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (fusedLabel 8 0 0 v)
theorem sourceMap1155_checked : acceptsGraphIso
    (source (graph core1155) (root 8) 0 0) DegreeOneSmallSpectrum360.graph sourceMap1155=true := by decide +kernel
theorem fusedMap1155_checked : acceptsGraphIso
    (fused (graph core1155) (root 8) 0 0) DegreeOneSmallSpectrum246.graph fusedMap1155=true := by decide +kernel
theorem certified1155 : Certified (graph core1155) (root 8) 0 0 :=
  of_native_maps core1155 DegreeOneSmallSpectrum360.graph DegreeOneSmallSpectrum246.graph
    sourceMap1155 fusedMap1155 sourceMap1155_checked fusedMap1155_checked
    DegreeOneSmallComparisons.comparison1155
#print axioms sourceMap1155_checked
#print axioms fusedMap1155_checked
#print axioms certified1155
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
