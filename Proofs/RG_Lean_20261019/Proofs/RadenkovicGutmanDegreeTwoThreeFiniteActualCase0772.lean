/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0772 : Family 10 := level10.get ⟨1143,by decide⟩
def sourceMap0772 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0772 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0772_checked : acceptsGraphIso
    (source (graph core0772) (root 10) 0 0) DegreeOneSmallSpectrum1794.graph sourceMap0772=true := by decide +kernel
theorem fusedMap0772_checked : acceptsGraphIso
    (fused (graph core0772) (root 10) 0 0) DegreeOneSmallSpectrum1757.graph fusedMap0772=true := by decide +kernel
theorem certified0772 : Certified (graph core0772) (root 10) 0 0 :=
  of_native_maps core0772 DegreeOneSmallSpectrum1794.graph DegreeOneSmallSpectrum1757.graph
    sourceMap0772 fusedMap0772 sourceMap0772_checked fusedMap0772_checked
    DegreeTwoThreeFiniteComparisons.comparison0772
#print axioms sourceMap0772_checked
#print axioms fusedMap0772_checked
#print axioms certified0772
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
