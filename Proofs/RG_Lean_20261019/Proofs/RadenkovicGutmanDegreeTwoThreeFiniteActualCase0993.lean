/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons19
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0993 : Family 10 := level10.get ⟨1702,by decide⟩
def sourceMap0993 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,5,6,7,8,9,10,11,12,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0993 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0993_checked : acceptsGraphIso
    (source (graph core0993) (root 10) 0 0) DegreeTwoThreeSpectrum1706.graph sourceMap0993=true := by decide +kernel
theorem fusedMap0993_checked : acceptsGraphIso
    (fused (graph core0993) (root 10) 0 0) DegreeOneSmallSpectrum1889.graph fusedMap0993=true := by decide +kernel
theorem certified0993 : Certified (graph core0993) (root 10) 0 0 :=
  of_native_maps core0993 DegreeTwoThreeSpectrum1706.graph DegreeOneSmallSpectrum1889.graph
    sourceMap0993 fusedMap0993 sourceMap0993_checked fusedMap0993_checked
    DegreeTwoThreeFiniteComparisons.comparison0993
#print axioms sourceMap0993_checked
#print axioms fusedMap0993_checked
#print axioms certified0993
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
