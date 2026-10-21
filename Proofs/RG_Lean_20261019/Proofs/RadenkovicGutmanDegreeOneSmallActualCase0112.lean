/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons02
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0112 : Family 4 := level4.get ⟨1,by decide⟩
def sourceMap0112 : (Vertices 4 ⊕ Fin 1 ⊕ Fin 2) → Fin 8 :=
  fun v => ![4,0,1,2,3,7,5,6] (sourceLabel 4 0 1 v)
def fusedMap0112 : (Vertices 4 ⊕ Fin 3) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (fusedLabel 4 0 1 v)
theorem sourceMap0112_checked : acceptsGraphIso
    (source (graph core0112) (root 4) 0 1) DegreeOneSmallSpectrum020.graph sourceMap0112=true := by decide +kernel
theorem fusedMap0112_checked : acceptsGraphIso
    (fused (graph core0112) (root 4) 0 1) DegreeOneSmallSpectrum021.graph fusedMap0112=true := by decide +kernel
theorem certified0112 : Certified (graph core0112) (root 4) 0 1 :=
  of_native_maps core0112 DegreeOneSmallSpectrum020.graph DegreeOneSmallSpectrum021.graph
    sourceMap0112 fusedMap0112 sourceMap0112_checked fusedMap0112_checked
    DegreeOneSmallComparisons.comparison0112
#print axioms sourceMap0112_checked
#print axioms fusedMap0112_checked
#print axioms certified0112
def sourceMap0112swap : (Vertices 4 ⊕ Fin 2 ⊕ Fin 1) → Fin 8 :=
  fun v => ![4,0,1,2,3,5,6,7] (sourceLabel 4 1 0 v)
def fusedMap0112swap : (Vertices 4 ⊕ Fin 3) → Fin 8 :=
  fun v => ![0,1,2,3,4,5,6,7] (fusedLabel 4 1 0 v)
theorem sourceMap0112swap_checked : acceptsGraphIso
    (source (graph core0112) (root 4) 1 0) DegreeOneSmallSpectrum020.graph sourceMap0112swap=true := by decide +kernel
theorem fusedMap0112swap_checked : acceptsGraphIso
    (fused (graph core0112) (root 4) 1 0) DegreeOneSmallSpectrum021.graph fusedMap0112swap=true := by decide +kernel
theorem certified0112swap : Certified (graph core0112) (root 4) 1 0 :=
  of_native_maps core0112 DegreeOneSmallSpectrum020.graph DegreeOneSmallSpectrum021.graph
    sourceMap0112swap fusedMap0112swap sourceMap0112swap_checked fusedMap0112swap_checked
    DegreeOneSmallComparisons.comparison0112
#print axioms sourceMap0112swap_checked
#print axioms fusedMap0112swap_checked
#print axioms certified0112swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
