/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1804 : Family 10 := level10.get ⟨42,by decide⟩
def sourceMap1804 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,7,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1804 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap1804_checked : acceptsGraphIso
    (source (graph core1804) (root 10) 0 0) DegreeOneSmallSpectrum874.graph sourceMap1804=true := by decide +kernel
theorem fusedMap1804_checked : acceptsGraphIso
    (fused (graph core1804) (root 10) 0 0) DegreeOneSmallSpectrum966.graph fusedMap1804=true := by decide +kernel
theorem certified1804 : Certified (graph core1804) (root 10) 0 0 :=
  of_native_maps core1804 DegreeOneSmallSpectrum874.graph DegreeOneSmallSpectrum966.graph
    sourceMap1804 fusedMap1804 sourceMap1804_checked fusedMap1804_checked
    DegreeOneSmallComparisons.comparison1804
#print axioms sourceMap1804_checked
#print axioms fusedMap1804_checked
#print axioms certified1804
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
