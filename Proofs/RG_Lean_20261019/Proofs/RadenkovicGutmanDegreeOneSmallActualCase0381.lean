/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0381 : Family 6 := level6.get ⟨15,by decide⟩
def sourceMap0381 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,4,5,1,2,3] (sourceLabel 6 1 2 v)
def fusedMap0381 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 1 2 v)
theorem sourceMap0381_checked : acceptsGraphIso
    (source (graph core0381) (root 6) 1 2) DegreeOneSmallSpectrum573.graph sourceMap0381=true := by decide +kernel
theorem fusedMap0381_checked : acceptsGraphIso
    (fused (graph core0381) (root 6) 1 2) DegreeOneSmallSpectrum388.graph fusedMap0381=true := by decide +kernel
theorem certified0381 : Certified (graph core0381) (root 6) 1 2 :=
  of_native_maps core0381 DegreeOneSmallSpectrum573.graph DegreeOneSmallSpectrum388.graph
    sourceMap0381 fusedMap0381 sourceMap0381_checked fusedMap0381_checked
    DegreeOneSmallComparisons.comparison0381
#print axioms sourceMap0381_checked
#print axioms fusedMap0381_checked
#print axioms certified0381
def sourceMap0381swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![0,6,7,8,9,10,11,1,2,3,4,5] (sourceLabel 6 2 1 v)
def fusedMap0381swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 2 1 v)
theorem sourceMap0381swap_checked : acceptsGraphIso
    (source (graph core0381) (root 6) 2 1) DegreeOneSmallSpectrum573.graph sourceMap0381swap=true := by decide +kernel
theorem fusedMap0381swap_checked : acceptsGraphIso
    (fused (graph core0381) (root 6) 2 1) DegreeOneSmallSpectrum388.graph fusedMap0381swap=true := by decide +kernel
theorem certified0381swap : Certified (graph core0381) (root 6) 2 1 :=
  of_native_maps core0381 DegreeOneSmallSpectrum573.graph DegreeOneSmallSpectrum388.graph
    sourceMap0381swap fusedMap0381swap sourceMap0381swap_checked fusedMap0381swap_checked
    DegreeOneSmallComparisons.comparison0381
#print axioms sourceMap0381swap_checked
#print axioms fusedMap0381swap_checked
#print axioms certified0381swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
