/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0412 : Family 6 := level6.get ⟨23,by decide⟩
def sourceMap0412 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (sourceLabel 6 0 1 v)
def fusedMap0412 : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 6 0 1 v)
theorem sourceMap0412_checked : acceptsGraphIso
    (source (graph core0412) (root 6) 0 1) DegreeOneSmallSpectrum114.graph sourceMap0412=true := by decide +kernel
theorem fusedMap0412_checked : acceptsGraphIso
    (fused (graph core0412) (root 6) 0 1) DegreeOneSmallSpectrum115.graph fusedMap0412=true := by decide +kernel
theorem certified0412 : Certified (graph core0412) (root 6) 0 1 :=
  of_native_maps core0412 DegreeOneSmallSpectrum114.graph DegreeOneSmallSpectrum115.graph
    sourceMap0412 fusedMap0412 sourceMap0412_checked fusedMap0412_checked
    DegreeOneSmallComparisons.comparison0412
#print axioms sourceMap0412_checked
#print axioms fusedMap0412_checked
#print axioms certified0412
def sourceMap0412swap : (Vertices 6 ⊕ Fin 2 ⊕ Fin 1) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (sourceLabel 6 1 0 v)
def fusedMap0412swap : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 6 1 0 v)
theorem sourceMap0412swap_checked : acceptsGraphIso
    (source (graph core0412) (root 6) 1 0) DegreeOneSmallSpectrum114.graph sourceMap0412swap=true := by decide +kernel
theorem fusedMap0412swap_checked : acceptsGraphIso
    (fused (graph core0412) (root 6) 1 0) DegreeOneSmallSpectrum115.graph fusedMap0412swap=true := by decide +kernel
theorem certified0412swap : Certified (graph core0412) (root 6) 1 0 :=
  of_native_maps core0412 DegreeOneSmallSpectrum114.graph DegreeOneSmallSpectrum115.graph
    sourceMap0412swap fusedMap0412swap sourceMap0412swap_checked fusedMap0412swap_checked
    DegreeOneSmallComparisons.comparison0412
#print axioms sourceMap0412swap_checked
#print axioms fusedMap0412swap_checked
#print axioms certified0412swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
