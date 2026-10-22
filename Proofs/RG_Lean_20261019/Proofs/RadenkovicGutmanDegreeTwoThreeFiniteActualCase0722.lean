/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons14
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0722 : Family 10 := level10.get ⟨1017,by decide⟩
def sourceMap0722 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,12,9,10,11] (sourceLabel 10 0 0 v)
def fusedMap0722 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,11,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap0722_checked : acceptsGraphIso
    (source (graph core0722) (root 10) 0 0) DegreeTwoThreeSpectrum1328.graph sourceMap0722=true := by decide +kernel
theorem fusedMap0722_checked : acceptsGraphIso
    (fused (graph core0722) (root 10) 0 0) DegreeOneSmallSpectrum1583.graph fusedMap0722=true := by decide +kernel
theorem certified0722 : Certified (graph core0722) (root 10) 0 0 :=
  of_native_maps core0722 DegreeTwoThreeSpectrum1328.graph DegreeOneSmallSpectrum1583.graph
    sourceMap0722 fusedMap0722 sourceMap0722_checked fusedMap0722_checked
    DegreeTwoThreeFiniteComparisons.comparison0722
#print axioms sourceMap0722_checked
#print axioms fusedMap0722_checked
#print axioms certified0722
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
