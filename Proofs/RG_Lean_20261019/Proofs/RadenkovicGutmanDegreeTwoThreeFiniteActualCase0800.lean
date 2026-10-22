/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0800 : Family 10 := level10.get ⟨1209,by decide⟩
def sourceMap0800 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0800 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0800_checked : acceptsGraphIso
    (source (graph core0800) (root 10) 0 0) DegreeOneSmallSpectrum1797.graph sourceMap0800=true := by decide +kernel
theorem fusedMap0800_checked : acceptsGraphIso
    (fused (graph core0800) (root 10) 0 0) DegreeOneSmallSpectrum1760.graph fusedMap0800=true := by decide +kernel
theorem certified0800 : Certified (graph core0800) (root 10) 0 0 :=
  of_native_maps core0800 DegreeOneSmallSpectrum1797.graph DegreeOneSmallSpectrum1760.graph
    sourceMap0800 fusedMap0800 sourceMap0800_checked fusedMap0800_checked
    DegreeTwoThreeFiniteComparisons.comparison0800
#print axioms sourceMap0800_checked
#print axioms fusedMap0800_checked
#print axioms certified0800
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
