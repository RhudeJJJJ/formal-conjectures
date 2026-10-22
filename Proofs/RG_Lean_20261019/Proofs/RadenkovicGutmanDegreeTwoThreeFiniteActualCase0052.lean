/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0052 : Family 7 := level7.get ⟨77,by decide⟩
def sourceMap0052 : (Vertices 7 ⊕ Fin 1 ⊕ Fin 1) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (sourceLabel 7 0 0 v)
def fusedMap0052 : (Vertices 7 ⊕ Fin 2) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 7 0 0 v)
theorem sourceMap0052_checked : acceptsGraphIso
    (source (graph core0052) (root 7) 0 0) DegreeOneSmallSpectrum129.graph sourceMap0052=true := by decide +kernel
theorem fusedMap0052_checked : acceptsGraphIso
    (fused (graph core0052) (root 7) 0 0) DegreeOneSmallSpectrum128.graph fusedMap0052=true := by decide +kernel
theorem certified0052 : Certified (graph core0052) (root 7) 0 0 :=
  of_native_maps core0052 DegreeOneSmallSpectrum129.graph DegreeOneSmallSpectrum128.graph
    sourceMap0052 fusedMap0052 sourceMap0052_checked fusedMap0052_checked
    DegreeTwoThreeFiniteComparisons.comparison0052
#print axioms sourceMap0052_checked
#print axioms fusedMap0052_checked
#print axioms certified0052
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
