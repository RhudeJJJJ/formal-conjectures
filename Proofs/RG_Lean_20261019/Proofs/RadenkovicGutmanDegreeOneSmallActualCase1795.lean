/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1795 : Family 10 := level10.get ⟨31,by decide⟩
def sourceMap1795 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1795 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap1795_checked : acceptsGraphIso
    (source (graph core1795) (root 10) 0 0) DegreeOneSmallSpectrum877.graph sourceMap1795=true := by decide +kernel
theorem fusedMap1795_checked : acceptsGraphIso
    (fused (graph core1795) (root 10) 0 0) DegreeOneSmallSpectrum962.graph fusedMap1795=true := by decide +kernel
theorem certified1795 : Certified (graph core1795) (root 10) 0 0 :=
  of_native_maps core1795 DegreeOneSmallSpectrum877.graph DegreeOneSmallSpectrum962.graph
    sourceMap1795 fusedMap1795 sourceMap1795_checked fusedMap1795_checked
    DegreeOneSmallComparisons.comparison1795
#print axioms sourceMap1795_checked
#print axioms fusedMap1795_checked
#print axioms certified1795
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
