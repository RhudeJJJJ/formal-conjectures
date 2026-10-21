/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0354 : Family 6 := level6.get ⟨11,by decide⟩
def sourceMap0354 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 6 1 2 v)
def fusedMap0354 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 1 2 v)
theorem sourceMap0354_checked : acceptsGraphIso
    (source (graph core0354) (root 6) 1 2) DegreeOneSmallSpectrum531.graph sourceMap0354=true := by decide +kernel
theorem fusedMap0354_checked : acceptsGraphIso
    (fused (graph core0354) (root 6) 1 2) DegreeOneSmallSpectrum380.graph fusedMap0354=true := by decide +kernel
theorem certified0354 : Certified (graph core0354) (root 6) 1 2 :=
  of_native_maps core0354 DegreeOneSmallSpectrum531.graph DegreeOneSmallSpectrum380.graph
    sourceMap0354 fusedMap0354 sourceMap0354_checked fusedMap0354_checked
    DegreeOneSmallComparisons.comparison0354
#print axioms sourceMap0354_checked
#print axioms fusedMap0354_checked
#print axioms certified0354
def sourceMap0354swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (sourceLabel 6 2 1 v)
def fusedMap0354swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 2 1 v)
theorem sourceMap0354swap_checked : acceptsGraphIso
    (source (graph core0354) (root 6) 2 1) DegreeOneSmallSpectrum531.graph sourceMap0354swap=true := by decide +kernel
theorem fusedMap0354swap_checked : acceptsGraphIso
    (fused (graph core0354) (root 6) 2 1) DegreeOneSmallSpectrum380.graph fusedMap0354swap=true := by decide +kernel
theorem certified0354swap : Certified (graph core0354) (root 6) 2 1 :=
  of_native_maps core0354 DegreeOneSmallSpectrum531.graph DegreeOneSmallSpectrum380.graph
    sourceMap0354swap fusedMap0354swap sourceMap0354swap_checked fusedMap0354swap_checked
    DegreeOneSmallComparisons.comparison0354
#print axioms sourceMap0354swap_checked
#print axioms fusedMap0354swap_checked
#print axioms certified0354swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
