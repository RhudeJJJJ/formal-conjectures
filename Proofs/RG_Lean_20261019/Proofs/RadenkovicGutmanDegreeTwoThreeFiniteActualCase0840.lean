/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0840 : Family 10 := level10.get ⟨1310,by decide⟩
def sourceMap0840 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,5,6,2,3,4] (sourceLabel 10 0 0 v)
def fusedMap0840 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,11,12,10,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap0840_checked : acceptsGraphIso
    (source (graph core0840) (root 10) 0 0) DegreeTwoThreeSpectrum1413.graph sourceMap0840=true := by decide +kernel
theorem fusedMap0840_checked : acceptsGraphIso
    (fused (graph core0840) (root 10) 0 0) DegreeOneSmallSpectrum1941.graph fusedMap0840=true := by decide +kernel
theorem certified0840 : Certified (graph core0840) (root 10) 0 0 :=
  of_native_maps core0840 DegreeTwoThreeSpectrum1413.graph DegreeOneSmallSpectrum1941.graph
    sourceMap0840 fusedMap0840 sourceMap0840_checked fusedMap0840_checked
    DegreeTwoThreeFiniteComparisons.comparison0840
#print axioms sourceMap0840_checked
#print axioms fusedMap0840_checked
#print axioms certified0840
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
