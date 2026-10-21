/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons37
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1893 : Family 10 := level10.get ⟨165,by decide⟩
def sourceMap1893 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,9,10,11,12,6,7,8,4,5] (sourceLabel 10 0 0 v)
def fusedMap1893 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap1893_checked : acceptsGraphIso
    (source (graph core1893) (root 10) 0 0) DegreeOneSmallSpectrum1195.graph sourceMap1893=true := by decide +kernel
theorem fusedMap1893_checked : acceptsGraphIso
    (fused (graph core1893) (root 10) 0 0) DegreeOneSmallSpectrum968.graph fusedMap1893=true := by decide +kernel
theorem certified1893 : Certified (graph core1893) (root 10) 0 0 :=
  of_native_maps core1893 DegreeOneSmallSpectrum1195.graph DegreeOneSmallSpectrum968.graph
    sourceMap1893 fusedMap1893 sourceMap1893_checked fusedMap1893_checked
    DegreeOneSmallComparisons.comparison1893
#print axioms sourceMap1893_checked
#print axioms fusedMap1893_checked
#print axioms certified1893
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
