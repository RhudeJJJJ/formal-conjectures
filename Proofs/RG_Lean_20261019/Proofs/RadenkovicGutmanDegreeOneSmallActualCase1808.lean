/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1808 : Family 10 := level10.get ⟨48,by decide⟩
def sourceMap1808 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,6,7,4,5] (sourceLabel 10 0 0 v)
def fusedMap1808 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,6,7,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap1808_checked : acceptsGraphIso
    (source (graph core1808) (root 10) 0 0) DegreeOneSmallSpectrum871.graph sourceMap1808=true := by decide +kernel
theorem fusedMap1808_checked : acceptsGraphIso
    (fused (graph core1808) (root 10) 0 0) DegreeOneSmallSpectrum951.graph fusedMap1808=true := by decide +kernel
theorem certified1808 : Certified (graph core1808) (root 10) 0 0 :=
  of_native_maps core1808 DegreeOneSmallSpectrum871.graph DegreeOneSmallSpectrum951.graph
    sourceMap1808 fusedMap1808 sourceMap1808_checked fusedMap1808_checked
    DegreeOneSmallComparisons.comparison1808
#print axioms sourceMap1808_checked
#print axioms fusedMap1808_checked
#print axioms certified1808
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
