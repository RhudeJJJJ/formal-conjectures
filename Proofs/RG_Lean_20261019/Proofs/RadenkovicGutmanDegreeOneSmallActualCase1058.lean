/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons21
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1058 : Family 8 := level8.get ⟨124,by decide⟩
def sourceMap1058 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,10,11,12,6,7,8,9] (sourceLabel 8 1 1 v)
def fusedMap1058 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1058_checked : acceptsGraphIso
    (source (graph core1058) (root 8) 1 1) DegreeOneSmallSpectrum1859.graph sourceMap1058=true := by decide +kernel
theorem fusedMap1058_checked : acceptsGraphIso
    (fused (graph core1058) (root 8) 1 1) DegreeOneSmallSpectrum1216.graph fusedMap1058=true := by decide +kernel
theorem certified1058 : Certified (graph core1058) (root 8) 1 1 :=
  of_native_maps core1058 DegreeOneSmallSpectrum1859.graph DegreeOneSmallSpectrum1216.graph
    sourceMap1058 fusedMap1058 sourceMap1058_checked fusedMap1058_checked
    DegreeOneSmallComparisons.comparison1058
#print axioms sourceMap1058_checked
#print axioms fusedMap1058_checked
#print axioms certified1058
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
