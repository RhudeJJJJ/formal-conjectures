/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0926 : Family 10 := level10.get ⟨1525,by decide⟩
def sourceMap0926 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0926 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0926_checked : acceptsGraphIso
    (source (graph core0926) (root 10) 0 0) DegreeTwoThreeSpectrum1682.graph sourceMap0926=true := by decide +kernel
theorem fusedMap0926_checked : acceptsGraphIso
    (fused (graph core0926) (root 10) 0 0) DegreeOneSmallSpectrum1520.graph fusedMap0926=true := by decide +kernel
theorem certified0926 : Certified (graph core0926) (root 10) 0 0 :=
  of_native_maps core0926 DegreeTwoThreeSpectrum1682.graph DegreeOneSmallSpectrum1520.graph
    sourceMap0926 fusedMap0926 sourceMap0926_checked fusedMap0926_checked
    DegreeTwoThreeFiniteComparisons.comparison0926
#print axioms sourceMap0926_checked
#print axioms fusedMap0926_checked
#print axioms certified0926
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
