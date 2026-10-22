/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0885 : Family 10 := level10.get ⟨1413,by decide⟩
def sourceMap0885 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0885 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0885_checked : acceptsGraphIso
    (source (graph core0885) (root 10) 0 0) DegreeOneSmallSpectrum1461.graph sourceMap0885=true := by decide +kernel
theorem fusedMap0885_checked : acceptsGraphIso
    (fused (graph core0885) (root 10) 0 0) DegreeOneSmallSpectrum1460.graph fusedMap0885=true := by decide +kernel
theorem certified0885 : Certified (graph core0885) (root 10) 0 0 :=
  of_native_maps core0885 DegreeOneSmallSpectrum1461.graph DegreeOneSmallSpectrum1460.graph
    sourceMap0885 fusedMap0885 sourceMap0885_checked fusedMap0885_checked
    DegreeTwoThreeFiniteComparisons.comparison0885
#print axioms sourceMap0885_checked
#print axioms fusedMap0885_checked
#print axioms certified0885
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
