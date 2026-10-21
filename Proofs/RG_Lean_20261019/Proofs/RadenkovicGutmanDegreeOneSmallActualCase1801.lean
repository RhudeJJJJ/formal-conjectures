/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1801 : Family 10 := level10.get ⟨39,by decide⟩
def sourceMap1801 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,6,7,4,5] (sourceLabel 10 0 0 v)
def fusedMap1801 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,6,7,8,9,10,11,12,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap1801_checked : acceptsGraphIso
    (source (graph core1801) (root 10) 0 0) DegreeOneSmallSpectrum888.graph sourceMap1801=true := by decide +kernel
theorem fusedMap1801_checked : acceptsGraphIso
    (fused (graph core1801) (root 10) 0 0) DegreeOneSmallSpectrum977.graph fusedMap1801=true := by decide +kernel
theorem certified1801 : Certified (graph core1801) (root 10) 0 0 :=
  of_native_maps core1801 DegreeOneSmallSpectrum888.graph DegreeOneSmallSpectrum977.graph
    sourceMap1801 fusedMap1801 sourceMap1801_checked fusedMap1801_checked
    DegreeOneSmallComparisons.comparison1801
#print axioms sourceMap1801_checked
#print axioms fusedMap1801_checked
#print axioms certified1801
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
