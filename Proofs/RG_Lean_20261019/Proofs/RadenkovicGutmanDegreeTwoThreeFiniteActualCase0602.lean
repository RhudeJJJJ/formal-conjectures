/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons12
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0602 : Family 10 := level10.get ⟨698,by decide⟩
def sourceMap0602 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (sourceLabel 10 0 0 v)
def fusedMap0602 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,9,10,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap0602_checked : acceptsGraphIso
    (source (graph core0602) (root 10) 0 0) DegreeTwoThreeSpectrum1091.graph sourceMap0602=true := by decide +kernel
theorem fusedMap0602_checked : acceptsGraphIso
    (fused (graph core0602) (root 10) 0 0) DegreeOneSmallSpectrum1307.graph fusedMap0602=true := by decide +kernel
theorem certified0602 : Certified (graph core0602) (root 10) 0 0 :=
  of_native_maps core0602 DegreeTwoThreeSpectrum1091.graph DegreeOneSmallSpectrum1307.graph
    sourceMap0602 fusedMap0602 sourceMap0602_checked fusedMap0602_checked
    DegreeTwoThreeFiniteComparisons.comparison0602
#print axioms sourceMap0602_checked
#print axioms fusedMap0602_checked
#print axioms certified0602
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
