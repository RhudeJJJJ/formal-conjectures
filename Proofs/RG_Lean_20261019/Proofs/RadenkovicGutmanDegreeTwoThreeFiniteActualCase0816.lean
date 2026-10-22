/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0816 : Family 10 := level10.get ⟨1251,by decide⟩
def sourceMap0816 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0816 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0816_checked : acceptsGraphIso
    (source (graph core0816) (root 10) 0 0) DegreeTwoThreeSpectrum1460.graph sourceMap0816=true := by decide +kernel
theorem fusedMap0816_checked : acceptsGraphIso
    (fused (graph core0816) (root 10) 0 0) DegreeOneSmallSpectrum1902.graph fusedMap0816=true := by decide +kernel
theorem certified0816 : Certified (graph core0816) (root 10) 0 0 :=
  of_native_maps core0816 DegreeTwoThreeSpectrum1460.graph DegreeOneSmallSpectrum1902.graph
    sourceMap0816 fusedMap0816 sourceMap0816_checked fusedMap0816_checked
    DegreeTwoThreeFiniteComparisons.comparison0816
#print axioms sourceMap0816_checked
#print axioms fusedMap0816_checked
#print axioms certified0816
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
