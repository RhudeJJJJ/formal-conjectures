/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1773 : Family 10 := level10.get ⟨6,by decide⟩
def sourceMap1773 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![4,3,2,1,0,8,9,10,11,12,7,5,6] (sourceLabel 10 0 0 v)
def fusedMap1773 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap1773_checked : acceptsGraphIso
    (source (graph core1773) (root 10) 0 0) DegreeOneSmallSpectrum894.graph sourceMap1773=true := by decide +kernel
theorem fusedMap1773_checked : acceptsGraphIso
    (fused (graph core1773) (root 10) 0 0) DegreeOneSmallSpectrum860.graph fusedMap1773=true := by decide +kernel
theorem certified1773 : Certified (graph core1773) (root 10) 0 0 :=
  of_native_maps core1773 DegreeOneSmallSpectrum894.graph DegreeOneSmallSpectrum860.graph
    sourceMap1773 fusedMap1773 sourceMap1773_checked fusedMap1773_checked
    DegreeOneSmallComparisons.comparison1773
#print axioms sourceMap1773_checked
#print axioms fusedMap1773_checked
#print axioms certified1773
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
