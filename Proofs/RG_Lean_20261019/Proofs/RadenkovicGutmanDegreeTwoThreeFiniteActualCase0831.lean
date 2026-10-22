/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0831 : Family 10 := level10.get ⟨1285,by decide⟩
def sourceMap0831 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (sourceLabel 10 0 0 v)
def fusedMap0831 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,7,8,9,10,11,12,2,3,4,5,6] (fusedLabel 10 0 0 v)
theorem sourceMap0831_checked : acceptsGraphIso
    (source (graph core0831) (root 10) 0 0) DegreeOneSmallSpectrum1801.graph sourceMap0831=true := by decide +kernel
theorem fusedMap0831_checked : acceptsGraphIso
    (fused (graph core0831) (root 10) 0 0) DegreeOneSmallSpectrum1764.graph fusedMap0831=true := by decide +kernel
theorem certified0831 : Certified (graph core0831) (root 10) 0 0 :=
  of_native_maps core0831 DegreeOneSmallSpectrum1801.graph DegreeOneSmallSpectrum1764.graph
    sourceMap0831 fusedMap0831 sourceMap0831_checked fusedMap0831_checked
    DegreeTwoThreeFiniteComparisons.comparison0831
#print axioms sourceMap0831_checked
#print axioms fusedMap0831_checked
#print axioms certified0831
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
