/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0877 : Family 10 := level10.get ⟨1390,by decide⟩
def sourceMap0877 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (sourceLabel 10 0 0 v)
def fusedMap0877 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![0,8,9,10,11,12,1,2,3,4,5,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap0877_checked : acceptsGraphIso
    (source (graph core0877) (root 10) 0 0) DegreeOneSmallSpectrum1047.graph sourceMap0877=true := by decide +kernel
theorem fusedMap0877_checked : acceptsGraphIso
    (fused (graph core0877) (root 10) 0 0) DegreeOneSmallSpectrum1042.graph fusedMap0877=true := by decide +kernel
theorem certified0877 : Certified (graph core0877) (root 10) 0 0 :=
  of_native_maps core0877 DegreeOneSmallSpectrum1047.graph DegreeOneSmallSpectrum1042.graph
    sourceMap0877 fusedMap0877 sourceMap0877_checked fusedMap0877_checked
    DegreeTwoThreeFiniteComparisons.comparison0877
#print axioms sourceMap0877_checked
#print axioms fusedMap0877_checked
#print axioms certified0877
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
