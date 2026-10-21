/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1931 : Family 10 := level10.get ⟨224,by decide⟩
def sourceMap1931 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap1931 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1931_checked : acceptsGraphIso
    (source (graph core1931) (root 10) 0 0) DegreeOneSmallSpectrum1125.graph sourceMap1931=true := by decide +kernel
theorem fusedMap1931_checked : acceptsGraphIso
    (fused (graph core1931) (root 10) 0 0) DegreeOneSmallSpectrum1134.graph fusedMap1931=true := by decide +kernel
theorem certified1931 : Certified (graph core1931) (root 10) 0 0 :=
  of_native_maps core1931 DegreeOneSmallSpectrum1125.graph DegreeOneSmallSpectrum1134.graph
    sourceMap1931 fusedMap1931 sourceMap1931_checked fusedMap1931_checked
    DegreeOneSmallComparisons.comparison1931
#print axioms sourceMap1931_checked
#print axioms fusedMap1931_checked
#print axioms certified1931
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
