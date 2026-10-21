/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1900 : Family 10 := level10.get ⟨177,by decide⟩
def sourceMap1900 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![5,1,0,8,9,10,11,12,2,3,4,6,7] (sourceLabel 10 0 0 v)
def fusedMap1900 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap1900_checked : acceptsGraphIso
    (source (graph core1900) (root 10) 0 0) DegreeOneSmallSpectrum946.graph sourceMap1900=true := by decide +kernel
theorem fusedMap1900_checked : acceptsGraphIso
    (fused (graph core1900) (root 10) 0 0) DegreeOneSmallSpectrum945.graph fusedMap1900=true := by decide +kernel
theorem certified1900 : Certified (graph core1900) (root 10) 0 0 :=
  of_native_maps core1900 DegreeOneSmallSpectrum946.graph DegreeOneSmallSpectrum945.graph
    sourceMap1900 fusedMap1900 sourceMap1900_checked fusedMap1900_checked
    DegreeOneSmallComparisons.comparison1900
#print axioms sourceMap1900_checked
#print axioms fusedMap1900_checked
#print axioms certified1900
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
