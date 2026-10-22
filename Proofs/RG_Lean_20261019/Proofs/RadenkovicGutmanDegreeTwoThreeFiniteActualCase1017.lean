/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1017 : Family 10 := level10.get ⟨1802,by decide⟩
def sourceMap1017 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap1017 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1017_checked : acceptsGraphIso
    (source (graph core1017) (root 10) 0 0) DegreeTwoThreeSpectrum1684.graph sourceMap1017=true := by decide +kernel
theorem fusedMap1017_checked : acceptsGraphIso
    (fused (graph core1017) (root 10) 0 0) DegreeOneSmallSpectrum1992.graph fusedMap1017=true := by decide +kernel
theorem certified1017 : Certified (graph core1017) (root 10) 0 0 :=
  of_native_maps core1017 DegreeTwoThreeSpectrum1684.graph DegreeOneSmallSpectrum1992.graph
    sourceMap1017 fusedMap1017 sourceMap1017_checked fusedMap1017_checked
    DegreeTwoThreeFiniteComparisons.comparison1017
#print axioms sourceMap1017_checked
#print axioms fusedMap1017_checked
#print axioms certified1017
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
