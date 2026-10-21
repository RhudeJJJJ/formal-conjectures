/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons18
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0941 : Family 8 := level8.get ⟨71,by decide⟩
def sourceMap0941 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0941 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0941_checked : acceptsGraphIso
    (source (graph core0941) (root 8) 0 2) DegreeOneSmallSpectrum1474.graph sourceMap0941=true := by decide +kernel
theorem fusedMap0941_checked : acceptsGraphIso
    (fused (graph core0941) (root 8) 0 2) DegreeOneSmallSpectrum946.graph fusedMap0941=true := by decide +kernel
theorem certified0941 : Certified (graph core0941) (root 8) 0 2 :=
  of_native_maps core0941 DegreeOneSmallSpectrum1474.graph DegreeOneSmallSpectrum946.graph
    sourceMap0941 fusedMap0941 sourceMap0941_checked fusedMap0941_checked
    DegreeOneSmallComparisons.comparison0941
#print axioms sourceMap0941_checked
#print axioms fusedMap0941_checked
#print axioms certified0941
def sourceMap0941swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0941swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0941swap_checked : acceptsGraphIso
    (source (graph core0941) (root 8) 2 0) DegreeOneSmallSpectrum1474.graph sourceMap0941swap=true := by decide +kernel
theorem fusedMap0941swap_checked : acceptsGraphIso
    (fused (graph core0941) (root 8) 2 0) DegreeOneSmallSpectrum946.graph fusedMap0941swap=true := by decide +kernel
theorem certified0941swap : Certified (graph core0941) (root 8) 2 0 :=
  of_native_maps core0941 DegreeOneSmallSpectrum1474.graph DegreeOneSmallSpectrum946.graph
    sourceMap0941swap fusedMap0941swap sourceMap0941swap_checked fusedMap0941swap_checked
    DegreeOneSmallComparisons.comparison0941
#print axioms sourceMap0941swap_checked
#print axioms fusedMap0941swap_checked
#print axioms certified0941swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
