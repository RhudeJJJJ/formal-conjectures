/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0363 : Family 6 := level6.get ⟨12,by decide⟩
def sourceMap0363 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 3) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,10,11,7,8,9] (sourceLabel 6 1 2 v)
def fusedMap0363 : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 1 2 v)
theorem sourceMap0363_checked : acceptsGraphIso
    (source (graph core0363) (root 6) 1 2) DegreeOneSmallSpectrum547.graph sourceMap0363=true := by decide +kernel
theorem fusedMap0363_checked : acceptsGraphIso
    (fused (graph core0363) (root 6) 1 2) DegreeOneSmallSpectrum381.graph fusedMap0363=true := by decide +kernel
theorem certified0363 : Certified (graph core0363) (root 6) 1 2 :=
  of_native_maps core0363 DegreeOneSmallSpectrum547.graph DegreeOneSmallSpectrum381.graph
    sourceMap0363 fusedMap0363 sourceMap0363_checked fusedMap0363_checked
    DegreeOneSmallComparisons.comparison0363
#print axioms sourceMap0363_checked
#print axioms fusedMap0363_checked
#print axioms certified0363
def sourceMap0363swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 2) → Fin 12 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9,10,11] (sourceLabel 6 2 1 v)
def fusedMap0363swap : (Vertices 6 ⊕ Fin 5) → Fin 12 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11] (fusedLabel 6 2 1 v)
theorem sourceMap0363swap_checked : acceptsGraphIso
    (source (graph core0363) (root 6) 2 1) DegreeOneSmallSpectrum547.graph sourceMap0363swap=true := by decide +kernel
theorem fusedMap0363swap_checked : acceptsGraphIso
    (fused (graph core0363) (root 6) 2 1) DegreeOneSmallSpectrum381.graph fusedMap0363swap=true := by decide +kernel
theorem certified0363swap : Certified (graph core0363) (root 6) 2 1 :=
  of_native_maps core0363 DegreeOneSmallSpectrum547.graph DegreeOneSmallSpectrum381.graph
    sourceMap0363swap fusedMap0363swap sourceMap0363swap_checked fusedMap0363swap_checked
    DegreeOneSmallComparisons.comparison0363
#print axioms sourceMap0363swap_checked
#print axioms fusedMap0363swap_checked
#print axioms certified0363swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
