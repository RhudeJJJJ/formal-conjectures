/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0992 : Family 10 := level10.get ⟨1700,by decide⟩
def sourceMap0992 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0992 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0992_checked : acceptsGraphIso
    (source (graph core0992) (root 10) 0 0) DegreeTwoThreeSpectrum1705.graph sourceMap0992=true := by decide +kernel
theorem fusedMap0992_checked : acceptsGraphIso
    (fused (graph core0992) (root 10) 0 0) DegreeOneSmallSpectrum1886.graph fusedMap0992=true := by decide +kernel
theorem certified0992 : Certified (graph core0992) (root 10) 0 0 :=
  of_native_maps core0992 DegreeTwoThreeSpectrum1705.graph DegreeOneSmallSpectrum1886.graph
    sourceMap0992 fusedMap0992 sourceMap0992_checked fusedMap0992_checked
    DegreeTwoThreeFiniteComparisons.comparison0992
#print axioms sourceMap0992_checked
#print axioms fusedMap0992_checked
#print axioms certified0992
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
