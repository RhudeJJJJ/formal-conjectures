/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1000 : Family 10 := level10.get ⟨1714,by decide⟩
def sourceMap1000 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,6,7,8,9,10,11,12,1,2,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap1000 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,6,7,8,9,10,11,12,1,2,3,4,5] (fusedLabel 10 0 0 v)
theorem sourceMap1000_checked : acceptsGraphIso
    (source (graph core1000) (root 10) 0 0) DegreeOneSmallSpectrum1799.graph sourceMap1000=true := by decide +kernel
theorem fusedMap1000_checked : acceptsGraphIso
    (fused (graph core1000) (root 10) 0 0) DegreeOneSmallSpectrum1762.graph fusedMap1000=true := by decide +kernel
theorem certified1000 : Certified (graph core1000) (root 10) 0 0 :=
  of_native_maps core1000 DegreeOneSmallSpectrum1799.graph DegreeOneSmallSpectrum1762.graph
    sourceMap1000 fusedMap1000 sourceMap1000_checked fusedMap1000_checked
    DegreeTwoThreeFiniteComparisons.comparison1000
#print axioms sourceMap1000_checked
#print axioms fusedMap1000_checked
#print axioms certified1000
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
