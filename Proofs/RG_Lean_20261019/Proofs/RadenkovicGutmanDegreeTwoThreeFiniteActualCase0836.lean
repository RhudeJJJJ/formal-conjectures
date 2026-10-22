/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0836 : Family 10 := level10.get ⟨1299,by decide⟩
def sourceMap0836 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0836 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0836_checked : acceptsGraphIso
    (source (graph core0836) (root 10) 0 0) DegreeTwoThreeSpectrum1465.graph sourceMap0836=true := by decide +kernel
theorem fusedMap0836_checked : acceptsGraphIso
    (fused (graph core0836) (root 10) 0 0) DegreeOneSmallSpectrum1935.graph fusedMap0836=true := by decide +kernel
theorem certified0836 : Certified (graph core0836) (root 10) 0 0 :=
  of_native_maps core0836 DegreeTwoThreeSpectrum1465.graph DegreeOneSmallSpectrum1935.graph
    sourceMap0836 fusedMap0836 sourceMap0836_checked fusedMap0836_checked
    DegreeTwoThreeFiniteComparisons.comparison0836
#print axioms sourceMap0836_checked
#print axioms fusedMap0836_checked
#print axioms certified0836
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
