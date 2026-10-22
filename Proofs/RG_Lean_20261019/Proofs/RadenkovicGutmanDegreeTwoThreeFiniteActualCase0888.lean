/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0888 : Family 10 := level10.get ⟨1422,by decide⟩
def sourceMap0888 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,10,11,12,5,6,7,8,9,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0888 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,4,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap0888_checked : acceptsGraphIso
    (source (graph core0888) (root 10) 0 0) DegreeOneSmallSpectrum1601.graph sourceMap0888=true := by decide +kernel
theorem fusedMap0888_checked : acceptsGraphIso
    (fused (graph core0888) (root 10) 0 0) DegreeOneSmallSpectrum1966.graph fusedMap0888=true := by decide +kernel
theorem certified0888 : Certified (graph core0888) (root 10) 0 0 :=
  of_native_maps core0888 DegreeOneSmallSpectrum1601.graph DegreeOneSmallSpectrum1966.graph
    sourceMap0888 fusedMap0888 sourceMap0888_checked fusedMap0888_checked
    DegreeTwoThreeFiniteComparisons.comparison0888
#print axioms sourceMap0888_checked
#print axioms fusedMap0888_checked
#print axioms certified0888
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
