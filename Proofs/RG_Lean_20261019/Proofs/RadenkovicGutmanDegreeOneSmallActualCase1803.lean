/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1803 : Family 10 := level10.get ⟨41,by decide⟩
def sourceMap1803 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,7,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1803 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap1803_checked : acceptsGraphIso
    (source (graph core1803) (root 10) 0 0) DegreeOneSmallSpectrum882.graph sourceMap1803=true := by decide +kernel
theorem fusedMap1803_checked : acceptsGraphIso
    (fused (graph core1803) (root 10) 0 0) DegreeOneSmallSpectrum976.graph fusedMap1803=true := by decide +kernel
theorem certified1803 : Certified (graph core1803) (root 10) 0 0 :=
  of_native_maps core1803 DegreeOneSmallSpectrum882.graph DegreeOneSmallSpectrum976.graph
    sourceMap1803 fusedMap1803 sourceMap1803_checked fusedMap1803_checked
    DegreeOneSmallComparisons.comparison1803
#print axioms sourceMap1803_checked
#print axioms fusedMap1803_checked
#print axioms certified1803
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
