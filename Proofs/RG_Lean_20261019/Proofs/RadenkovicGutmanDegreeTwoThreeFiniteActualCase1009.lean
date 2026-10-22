/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1009 : Family 10 := level10.get ⟨1741,by decide⟩
def sourceMap1009 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,6,7,8,9,10,11,12,1,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap1009 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,6,7,8,9,10,11,12,1,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap1009_checked : acceptsGraphIso
    (source (graph core1009) (root 10) 0 0) DegreeOneSmallSpectrum1802.graph sourceMap1009=true := by decide +kernel
theorem fusedMap1009_checked : acceptsGraphIso
    (fused (graph core1009) (root 10) 0 0) DegreeOneSmallSpectrum1765.graph fusedMap1009=true := by decide +kernel
theorem certified1009 : Certified (graph core1009) (root 10) 0 0 :=
  of_native_maps core1009 DegreeOneSmallSpectrum1802.graph DegreeOneSmallSpectrum1765.graph
    sourceMap1009 fusedMap1009 sourceMap1009_checked fusedMap1009_checked
    DegreeTwoThreeFiniteComparisons.comparison1009
#print axioms sourceMap1009_checked
#print axioms fusedMap1009_checked
#print axioms certified1009
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
