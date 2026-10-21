/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1812 : Family 10 := level10.get ⟨55,by decide⟩
def sourceMap1812 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1812 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1812_checked : acceptsGraphIso
    (source (graph core1812) (root 10) 0 0) DegreeOneSmallSpectrum1052.graph sourceMap1812=true := by decide +kernel
theorem fusedMap1812_checked : acceptsGraphIso
    (fused (graph core1812) (root 10) 0 0) DegreeOneSmallSpectrum864.graph fusedMap1812=true := by decide +kernel
theorem certified1812 : Certified (graph core1812) (root 10) 0 0 :=
  of_native_maps core1812 DegreeOneSmallSpectrum1052.graph DegreeOneSmallSpectrum864.graph
    sourceMap1812 fusedMap1812 sourceMap1812_checked fusedMap1812_checked
    DegreeOneSmallComparisons.comparison1812
#print axioms sourceMap1812_checked
#print axioms fusedMap1812_checked
#print axioms certified1812
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
