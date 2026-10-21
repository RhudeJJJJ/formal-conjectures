/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1095 : Family 8 := level8.get ⟨149,by decide⟩
def sourceMap1095 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10] (sourceLabel 8 0 0 v)
def fusedMap1095 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![5,0,1,2,3,4,8,9,10,6,7] (fusedLabel 8 0 0 v)
theorem sourceMap1095_checked : acceptsGraphIso
    (source (graph core1095) (root 8) 0 0) DegreeOneSmallSpectrum342.graph sourceMap1095=true := by decide +kernel
theorem fusedMap1095_checked : acceptsGraphIso
    (fused (graph core1095) (root 8) 0 0) DegreeOneSmallSpectrum341.graph fusedMap1095=true := by decide +kernel
theorem certified1095 : Certified (graph core1095) (root 8) 0 0 :=
  of_native_maps core1095 DegreeOneSmallSpectrum342.graph DegreeOneSmallSpectrum341.graph
    sourceMap1095 fusedMap1095 sourceMap1095_checked fusedMap1095_checked
    DegreeOneSmallComparisons.comparison1095
#print axioms sourceMap1095_checked
#print axioms fusedMap1095_checked
#print axioms certified1095
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
