/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1977 : Family 10 := level10.get ⟨297,by decide⟩
def sourceMap1977 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,6,5,3,4] (sourceLabel 10 0 0 v)
def fusedMap1977 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1977_checked : acceptsGraphIso
    (source (graph core1977) (root 10) 0 0) DegreeOneSmallSpectrum1151.graph sourceMap1977=true := by decide +kernel
theorem fusedMap1977_checked : acceptsGraphIso
    (fused (graph core1977) (root 10) 0 0) DegreeOneSmallSpectrum1346.graph fusedMap1977=true := by decide +kernel
theorem certified1977 : Certified (graph core1977) (root 10) 0 0 :=
  of_native_maps core1977 DegreeOneSmallSpectrum1151.graph DegreeOneSmallSpectrum1346.graph
    sourceMap1977 fusedMap1977 sourceMap1977_checked fusedMap1977_checked
    DegreeOneSmallComparisons.comparison1977
#print axioms sourceMap1977_checked
#print axioms fusedMap1977_checked
#print axioms certified1977
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
