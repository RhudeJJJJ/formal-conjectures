/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1834 : Family 10 := level10.get ⟨82,by decide⟩
def sourceMap1834 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![3,2,1,0,8,9,10,11,12,6,7,4,5] (sourceLabel 10 0 0 v)
def fusedMap1834 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,6,0,1,2,3,4,5,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap1834_checked : acceptsGraphIso
    (source (graph core1834) (root 10) 0 0) DegreeOneSmallSpectrum1104.graph sourceMap1834=true := by decide +kernel
theorem fusedMap1834_checked : acceptsGraphIso
    (fused (graph core1834) (root 10) 0 0) DegreeOneSmallSpectrum901.graph fusedMap1834=true := by decide +kernel
theorem certified1834 : Certified (graph core1834) (root 10) 0 0 :=
  of_native_maps core1834 DegreeOneSmallSpectrum1104.graph DegreeOneSmallSpectrum901.graph
    sourceMap1834 fusedMap1834 sourceMap1834_checked fusedMap1834_checked
    DegreeOneSmallComparisons.comparison1834
#print axioms sourceMap1834_checked
#print axioms fusedMap1834_checked
#print axioms certified1834
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
