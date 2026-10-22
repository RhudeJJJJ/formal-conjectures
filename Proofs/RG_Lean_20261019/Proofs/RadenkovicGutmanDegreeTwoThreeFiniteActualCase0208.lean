/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0208 : Family 9 := level9.get ⟨190,by decide⟩
def sourceMap0208 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,8,9,10,11,6,7,3,4,5] (sourceLabel 9 0 0 v)
def fusedMap0208 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,5,0,1,2,3,4,10,11,9,7,8] (fusedLabel 9 0 0 v)
theorem sourceMap0208_checked : acceptsGraphIso
    (source (graph core0208) (root 9) 0 0) DegreeOneSmallSpectrum637.graph sourceMap0208=true := by decide +kernel
theorem fusedMap0208_checked : acceptsGraphIso
    (fused (graph core0208) (root 9) 0 0) DegreeOneSmallSpectrum487.graph fusedMap0208=true := by decide +kernel
theorem certified0208 : Certified (graph core0208) (root 9) 0 0 :=
  of_native_maps core0208 DegreeOneSmallSpectrum637.graph DegreeOneSmallSpectrum487.graph
    sourceMap0208 fusedMap0208 sourceMap0208_checked fusedMap0208_checked
    DegreeTwoThreeFiniteComparisons.comparison0208
#print axioms sourceMap0208_checked
#print axioms fusedMap0208_checked
#print axioms certified0208
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
