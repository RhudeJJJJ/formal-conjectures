/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons09
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0492 : Family 10 := level10.get ⟨370,by decide⟩
def sourceMap0492 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,3,4,5] (sourceLabel 10 0 0 v)
def fusedMap0492 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,6,7,8,9,10,11,12,5,3,4] (fusedLabel 10 0 0 v)
theorem sourceMap0492_checked : acceptsGraphIso
    (source (graph core0492) (root 10) 0 0) DegreeOneSmallSpectrum1074.graph sourceMap0492=true := by decide +kernel
theorem fusedMap0492_checked : acceptsGraphIso
    (fused (graph core0492) (root 10) 0 0) DegreeOneSmallSpectrum1439.graph fusedMap0492=true := by decide +kernel
theorem certified0492 : Certified (graph core0492) (root 10) 0 0 :=
  of_native_maps core0492 DegreeOneSmallSpectrum1074.graph DegreeOneSmallSpectrum1439.graph
    sourceMap0492 fusedMap0492 sourceMap0492_checked fusedMap0492_checked
    DegreeTwoThreeFiniteComparisons.comparison0492
#print axioms sourceMap0492_checked
#print axioms fusedMap0492_checked
#print axioms certified0492
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
