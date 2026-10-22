/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0292 : Family 9 := level9.get ⟨417,by decide⟩
def sourceMap0292 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,5,6,7,8,9,10,11,2,3,4] (sourceLabel 9 0 0 v)
def fusedMap0292 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,0,1,2,3,4,5,6,7,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap0292_checked : acceptsGraphIso
    (source (graph core0292) (root 9) 0 0) DegreeTwoThreeSpectrum584.graph sourceMap0292=true := by decide +kernel
theorem fusedMap0292_checked : acceptsGraphIso
    (fused (graph core0292) (root 9) 0 0) DegreeOneSmallSpectrum776.graph fusedMap0292=true := by decide +kernel
theorem certified0292 : Certified (graph core0292) (root 9) 0 0 :=
  of_native_maps core0292 DegreeTwoThreeSpectrum584.graph DegreeOneSmallSpectrum776.graph
    sourceMap0292 fusedMap0292 sourceMap0292_checked fusedMap0292_checked
    DegreeTwoThreeFiniteComparisons.comparison0292
#print axioms sourceMap0292_checked
#print axioms fusedMap0292_checked
#print axioms certified0292
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
