/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1826 : Family 10 := level10.get ⟨71,by decide⟩
def sourceMap1826 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,7,8,9,10,11,12,6,4,5] (sourceLabel 10 0 0 v)
def fusedMap1826 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1826_checked : acceptsGraphIso
    (source (graph core1826) (root 10) 0 0) DegreeOneSmallSpectrum1162.graph sourceMap1826=true := by decide +kernel
theorem fusedMap1826_checked : acceptsGraphIso
    (fused (graph core1826) (root 10) 0 0) DegreeOneSmallSpectrum885.graph fusedMap1826=true := by decide +kernel
theorem certified1826 : Certified (graph core1826) (root 10) 0 0 :=
  of_native_maps core1826 DegreeOneSmallSpectrum1162.graph DegreeOneSmallSpectrum885.graph
    sourceMap1826 fusedMap1826 sourceMap1826_checked fusedMap1826_checked
    DegreeOneSmallComparisons.comparison1826
#print axioms sourceMap1826_checked
#print axioms fusedMap1826_checked
#print axioms certified1826
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
