/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0057 : Family 3 := level3.get ⟨0,by decide⟩
def sourceMap0057 : (Vertices 3 ⊕ Fin 1 ⊕ Fin 3) → Fin 8 :=
  fun v => ![0,1,2,3,7,4,5,6] (sourceLabel 3 0 2 v)
def fusedMap0057 : (Vertices 3 ⊕ Fin 4) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (fusedLabel 3 0 2 v)
theorem sourceMap0057_checked : acceptsGraphIso
    (source (graph core0057) (root 3) 0 2) DegreeOneSmallSpectrum026.graph sourceMap0057=true := by decide +kernel
theorem fusedMap0057_checked : acceptsGraphIso
    (fused (graph core0057) (root 3) 0 2) DegreeOneSmallSpectrum016.graph fusedMap0057=true := by decide +kernel
theorem certified0057 : Certified (graph core0057) (root 3) 0 2 :=
  of_native_maps core0057 DegreeOneSmallSpectrum026.graph DegreeOneSmallSpectrum016.graph
    sourceMap0057 fusedMap0057 sourceMap0057_checked fusedMap0057_checked
    DegreeOneSmallComparisons.comparison0057
#print axioms sourceMap0057_checked
#print axioms fusedMap0057_checked
#print axioms certified0057
def sourceMap0057swap : (Vertices 3 ⊕ Fin 3 ⊕ Fin 1) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (sourceLabel 3 2 0 v)
def fusedMap0057swap : (Vertices 3 ⊕ Fin 4) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (fusedLabel 3 2 0 v)
theorem sourceMap0057swap_checked : acceptsGraphIso
    (source (graph core0057) (root 3) 2 0) DegreeOneSmallSpectrum026.graph sourceMap0057swap=true := by decide +kernel
theorem fusedMap0057swap_checked : acceptsGraphIso
    (fused (graph core0057) (root 3) 2 0) DegreeOneSmallSpectrum016.graph fusedMap0057swap=true := by decide +kernel
theorem certified0057swap : Certified (graph core0057) (root 3) 2 0 :=
  of_native_maps core0057 DegreeOneSmallSpectrum026.graph DegreeOneSmallSpectrum016.graph
    sourceMap0057swap fusedMap0057swap sourceMap0057swap_checked fusedMap0057swap_checked
    DegreeOneSmallComparisons.comparison0057
#print axioms sourceMap0057swap_checked
#print axioms fusedMap0057swap_checked
#print axioms certified0057swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
