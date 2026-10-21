/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0395 : Family 6 := level6.get ⟨20,by decide⟩
def sourceMap0395 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,10,7,8,9] (sourceLabel 6 0 2 v)
def fusedMap0395 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap0395_checked : acceptsGraphIso
    (source (graph core0395) (root 6) 0 2) DegreeOneSmallSpectrum258.graph sourceMap0395=true := by decide +kernel
theorem fusedMap0395_checked : acceptsGraphIso
    (fused (graph core0395) (root 6) 0 2) DegreeOneSmallSpectrum170.graph fusedMap0395=true := by decide +kernel
theorem certified0395 : Certified (graph core0395) (root 6) 0 2 :=
  of_native_maps core0395 DegreeOneSmallSpectrum258.graph DegreeOneSmallSpectrum170.graph
    sourceMap0395 fusedMap0395 sourceMap0395_checked fusedMap0395_checked
    DegreeOneSmallComparisons.comparison0395
#print axioms sourceMap0395_checked
#print axioms fusedMap0395_checked
#print axioms certified0395
def sourceMap0395swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 2 0 v)
def fusedMap0395swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap0395swap_checked : acceptsGraphIso
    (source (graph core0395) (root 6) 2 0) DegreeOneSmallSpectrum258.graph sourceMap0395swap=true := by decide +kernel
theorem fusedMap0395swap_checked : acceptsGraphIso
    (fused (graph core0395) (root 6) 2 0) DegreeOneSmallSpectrum170.graph fusedMap0395swap=true := by decide +kernel
theorem certified0395swap : Certified (graph core0395) (root 6) 2 0 :=
  of_native_maps core0395 DegreeOneSmallSpectrum258.graph DegreeOneSmallSpectrum170.graph
    sourceMap0395swap fusedMap0395swap sourceMap0395swap_checked fusedMap0395swap_checked
    DegreeOneSmallComparisons.comparison0395
#print axioms sourceMap0395swap_checked
#print axioms fusedMap0395swap_checked
#print axioms certified0395swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
