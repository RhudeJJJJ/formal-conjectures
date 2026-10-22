/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons13
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0686 : Family 10 := level10.get ⟨926,by decide⟩
def sourceMap0686 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0686 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0686_checked : acceptsGraphIso
    (source (graph core0686) (root 10) 0 0) DegreeOneSmallSpectrum1512.graph sourceMap0686=true := by decide +kernel
theorem fusedMap0686_checked : acceptsGraphIso
    (fused (graph core0686) (root 10) 0 0) DegreeOneSmallSpectrum1510.graph fusedMap0686=true := by decide +kernel
theorem certified0686 : Certified (graph core0686) (root 10) 0 0 :=
  of_native_maps core0686 DegreeOneSmallSpectrum1512.graph DegreeOneSmallSpectrum1510.graph
    sourceMap0686 fusedMap0686 sourceMap0686_checked fusedMap0686_checked
    DegreeTwoThreeFiniteComparisons.comparison0686
#print axioms sourceMap0686_checked
#print axioms fusedMap0686_checked
#print axioms certified0686
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
