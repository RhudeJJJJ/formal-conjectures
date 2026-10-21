/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0208 : Family 5 := level5.get ⟨5,by decide⟩
def sourceMap0208 : (Vertices 5 ⊕ Fin 1 ⊕ Fin 2) → Fin 9 :=
  fun v => ![5,0,1,2,3,4,8,6,7] (sourceLabel 5 0 1 v)
def fusedMap0208 : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 5 0 1 v)
theorem sourceMap0208_checked : acceptsGraphIso
    (source (graph core0208) (root 5) 0 1) DegreeOneSmallSpectrum041.graph sourceMap0208=true := by decide +kernel
theorem fusedMap0208_checked : acceptsGraphIso
    (fused (graph core0208) (root 5) 0 1) DegreeOneSmallSpectrum042.graph fusedMap0208=true := by decide +kernel
theorem certified0208 : Certified (graph core0208) (root 5) 0 1 :=
  of_native_maps core0208 DegreeOneSmallSpectrum041.graph DegreeOneSmallSpectrum042.graph
    sourceMap0208 fusedMap0208 sourceMap0208_checked fusedMap0208_checked
    DegreeOneSmallComparisons.comparison0208
#print axioms sourceMap0208_checked
#print axioms fusedMap0208_checked
#print axioms certified0208
def sourceMap0208swap : (Vertices 5 ⊕ Fin 2 ⊕ Fin 1) → Fin 9 :=
  fun v => ![5,0,1,2,3,4,6,7,8] (sourceLabel 5 1 0 v)
def fusedMap0208swap : (Vertices 5 ⊕ Fin 3) → Fin 9 :=
  fun v => ![0,1,2,3,4,5,6,7,8] (fusedLabel 5 1 0 v)
theorem sourceMap0208swap_checked : acceptsGraphIso
    (source (graph core0208) (root 5) 1 0) DegreeOneSmallSpectrum041.graph sourceMap0208swap=true := by decide +kernel
theorem fusedMap0208swap_checked : acceptsGraphIso
    (fused (graph core0208) (root 5) 1 0) DegreeOneSmallSpectrum042.graph fusedMap0208swap=true := by decide +kernel
theorem certified0208swap : Certified (graph core0208) (root 5) 1 0 :=
  of_native_maps core0208 DegreeOneSmallSpectrum041.graph DegreeOneSmallSpectrum042.graph
    sourceMap0208swap fusedMap0208swap sourceMap0208swap_checked fusedMap0208swap_checked
    DegreeOneSmallComparisons.comparison0208
#print axioms sourceMap0208swap_checked
#print axioms fusedMap0208swap_checked
#print axioms certified0208swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
