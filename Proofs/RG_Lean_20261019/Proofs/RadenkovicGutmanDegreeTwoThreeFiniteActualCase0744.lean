/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0744 : Family 10 := level10.get ⟨1075,by decide⟩
def sourceMap0744 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (sourceLabel 10 0 0 v)
def fusedMap0744 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0744_checked : acceptsGraphIso
    (source (graph core0744) (root 10) 0 0) DegreeTwoThreeSpectrum1468.graph sourceMap0744=true := by decide +kernel
theorem fusedMap0744_checked : acceptsGraphIso
    (fused (graph core0744) (root 10) 0 0) DegreeOneSmallSpectrum1685.graph fusedMap0744=true := by decide +kernel
theorem certified0744 : Certified (graph core0744) (root 10) 0 0 :=
  of_native_maps core0744 DegreeTwoThreeSpectrum1468.graph DegreeOneSmallSpectrum1685.graph
    sourceMap0744 fusedMap0744 sourceMap0744_checked fusedMap0744_checked
    DegreeTwoThreeFiniteComparisons.comparison0744
#print axioms sourceMap0744_checked
#print axioms fusedMap0744_checked
#print axioms certified0744
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
