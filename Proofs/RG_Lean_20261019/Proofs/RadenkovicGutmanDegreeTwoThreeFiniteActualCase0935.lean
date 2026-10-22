/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0935 : Family 10 := level10.get ⟨1547,by decide⟩
def sourceMap0935 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,10,11,12,7,8,9] (sourceLabel 10 0 0 v)
def fusedMap0935 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap0935_checked : acceptsGraphIso
    (source (graph core0935) (root 10) 0 0) DegreeTwoThreeSpectrum1693.graph sourceMap0935=true := by decide +kernel
theorem fusedMap0935_checked : acceptsGraphIso
    (fused (graph core0935) (root 10) 0 0) DegreeOneSmallSpectrum1562.graph fusedMap0935=true := by decide +kernel
theorem certified0935 : Certified (graph core0935) (root 10) 0 0 :=
  of_native_maps core0935 DegreeTwoThreeSpectrum1693.graph DegreeOneSmallSpectrum1562.graph
    sourceMap0935 fusedMap0935 sourceMap0935_checked fusedMap0935_checked
    DegreeTwoThreeFiniteComparisons.comparison0935
#print axioms sourceMap0935_checked
#print axioms fusedMap0935_checked
#print axioms certified0935
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
