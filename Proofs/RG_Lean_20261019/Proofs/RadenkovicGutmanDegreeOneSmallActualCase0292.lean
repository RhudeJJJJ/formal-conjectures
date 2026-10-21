/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0292 : Family 6 := level6.get ⟨2,by decide⟩
def sourceMap0292 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 4) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,11,12,7,8,9,10] (sourceLabel 6 1 3 v)
def fusedMap0292 : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 1 3 v)
theorem sourceMap0292_checked : acceptsGraphIso
    (source (graph core0292) (root 6) 1 3) DegreeOneSmallSpectrum941.graph sourceMap0292=true := by decide +kernel
theorem fusedMap0292_checked : acceptsGraphIso
    (fused (graph core0292) (root 6) 1 3) DegreeOneSmallSpectrum857.graph fusedMap0292=true := by decide +kernel
theorem certified0292 : Certified (graph core0292) (root 6) 1 3 :=
  of_native_maps core0292 DegreeOneSmallSpectrum941.graph DegreeOneSmallSpectrum857.graph
    sourceMap0292 fusedMap0292 sourceMap0292_checked fusedMap0292_checked
    DegreeOneSmallComparisons.comparison0292
#print axioms sourceMap0292_checked
#print axioms fusedMap0292_checked
#print axioms certified0292
def sourceMap0292swap : (Vertices 6 ⊕ Fin 4 ⊕ Fin 2) → Fin 13 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11,12] (sourceLabel 6 3 1 v)
def fusedMap0292swap : (Vertices 6 ⊕ Fin 6) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 6 3 1 v)
theorem sourceMap0292swap_checked : acceptsGraphIso
    (source (graph core0292) (root 6) 3 1) DegreeOneSmallSpectrum941.graph sourceMap0292swap=true := by decide +kernel
theorem fusedMap0292swap_checked : acceptsGraphIso
    (fused (graph core0292) (root 6) 3 1) DegreeOneSmallSpectrum857.graph fusedMap0292swap=true := by decide +kernel
theorem certified0292swap : Certified (graph core0292) (root 6) 3 1 :=
  of_native_maps core0292 DegreeOneSmallSpectrum941.graph DegreeOneSmallSpectrum857.graph
    sourceMap0292swap fusedMap0292swap sourceMap0292swap_checked fusedMap0292swap_checked
    DegreeOneSmallComparisons.comparison0292
#print axioms sourceMap0292swap_checked
#print axioms fusedMap0292swap_checked
#print axioms certified0292swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
