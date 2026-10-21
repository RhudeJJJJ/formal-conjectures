/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons06
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0331 : Family 6 := level6.get ⟨8,by decide⟩
def sourceMap0331 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 2) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,9,8,6,7] (sourceLabel 6 0 1 v)
def fusedMap0331 : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (fusedLabel 6 0 1 v)
theorem sourceMap0331_checked : acceptsGraphIso
    (source (graph core0331) (root 6) 0 1) DegreeOneSmallSpectrum127.graph sourceMap0331=true := by decide +kernel
theorem fusedMap0331_checked : acceptsGraphIso
    (fused (graph core0331) (root 6) 0 1) DegreeOneSmallSpectrum076.graph fusedMap0331=true := by decide +kernel
theorem certified0331 : Certified (graph core0331) (root 6) 0 1 :=
  of_native_maps core0331 DegreeOneSmallSpectrum127.graph DegreeOneSmallSpectrum076.graph
    sourceMap0331 fusedMap0331 sourceMap0331_checked fusedMap0331_checked
    DegreeOneSmallComparisons.comparison0331
#print axioms sourceMap0331_checked
#print axioms fusedMap0331_checked
#print axioms certified0331
def sourceMap0331swap : (Vertices 6 ⊕ Fin 2 ⊕ Fin 1) → Fin 10 :=
  fun v => ![5,0,1,2,3,4,9,6,7,8] (sourceLabel 6 1 0 v)
def fusedMap0331swap : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (fusedLabel 6 1 0 v)
theorem sourceMap0331swap_checked : acceptsGraphIso
    (source (graph core0331) (root 6) 1 0) DegreeOneSmallSpectrum127.graph sourceMap0331swap=true := by decide +kernel
theorem fusedMap0331swap_checked : acceptsGraphIso
    (fused (graph core0331) (root 6) 1 0) DegreeOneSmallSpectrum076.graph fusedMap0331swap=true := by decide +kernel
theorem certified0331swap : Certified (graph core0331) (root 6) 1 0 :=
  of_native_maps core0331 DegreeOneSmallSpectrum127.graph DegreeOneSmallSpectrum076.graph
    sourceMap0331swap fusedMap0331swap sourceMap0331swap_checked fusedMap0331swap_checked
    DegreeOneSmallComparisons.comparison0331
#print axioms sourceMap0331swap_checked
#print axioms fusedMap0331swap_checked
#print axioms certified0331swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
