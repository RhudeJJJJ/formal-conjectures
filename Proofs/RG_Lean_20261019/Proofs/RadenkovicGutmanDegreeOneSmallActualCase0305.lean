/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0305 : Family 6 := level6.get ⟨4,by decide⟩
def sourceMap0305 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,5,2,3,4] (sourceLabel 6 0 2 v)
def fusedMap0305 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap0305_checked : acceptsGraphIso
    (source (graph core0305) (root 6) 0 2) DegreeOneSmallSpectrum227.graph sourceMap0305=true := by decide +kernel
theorem fusedMap0305_checked : acceptsGraphIso
    (fused (graph core0305) (root 6) 0 2) DegreeOneSmallSpectrum167.graph fusedMap0305=true := by decide +kernel
theorem certified0305 : Certified (graph core0305) (root 6) 0 2 :=
  of_native_maps core0305 DegreeOneSmallSpectrum227.graph DegreeOneSmallSpectrum167.graph
    sourceMap0305 fusedMap0305 sourceMap0305_checked fusedMap0305_checked
    DegreeOneSmallComparisons.comparison0305
#print axioms sourceMap0305_checked
#print axioms fusedMap0305_checked
#print axioms certified0305
def sourceMap0305swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![1,0,6,7,8,9,10,2,3,4,5] (sourceLabel 6 2 0 v)
def fusedMap0305swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap0305swap_checked : acceptsGraphIso
    (source (graph core0305) (root 6) 2 0) DegreeOneSmallSpectrum227.graph sourceMap0305swap=true := by decide +kernel
theorem fusedMap0305swap_checked : acceptsGraphIso
    (fused (graph core0305) (root 6) 2 0) DegreeOneSmallSpectrum167.graph fusedMap0305swap=true := by decide +kernel
theorem certified0305swap : Certified (graph core0305) (root 6) 2 0 :=
  of_native_maps core0305 DegreeOneSmallSpectrum227.graph DegreeOneSmallSpectrum167.graph
    sourceMap0305swap fusedMap0305swap sourceMap0305swap_checked fusedMap0305swap_checked
    DegreeOneSmallComparisons.comparison0305
#print axioms sourceMap0305swap_checked
#print axioms fusedMap0305swap_checked
#print axioms certified0305swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
