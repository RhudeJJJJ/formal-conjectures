/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons39
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1956 : Family 10 := level10.get ⟨261,by decide⟩
def sourceMap1956 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap1956 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap1956_checked : acceptsGraphIso
    (source (graph core1956) (root 10) 0 0) DegreeOneSmallSpectrum1198.graph sourceMap1956=true := by decide +kernel
theorem fusedMap1956_checked : acceptsGraphIso
    (fused (graph core1956) (root 10) 0 0) DegreeOneSmallSpectrum1290.graph fusedMap1956=true := by decide +kernel
theorem certified1956 : Certified (graph core1956) (root 10) 0 0 :=
  of_native_maps core1956 DegreeOneSmallSpectrum1198.graph DegreeOneSmallSpectrum1290.graph
    sourceMap1956 fusedMap1956 sourceMap1956_checked fusedMap1956_checked
    DegreeOneSmallComparisons.comparison1956
#print axioms sourceMap1956_checked
#print axioms fusedMap1956_checked
#print axioms certified1956
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
