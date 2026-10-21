/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0385 : Family 6 := level6.get ⟨19,by decide⟩
def sourceMap0385 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 2) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,9,7,8] (sourceLabel 6 0 1 v)
def fusedMap0385 : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 6 0 1 v)
theorem sourceMap0385_checked : acceptsGraphIso
    (source (graph core0385) (root 6) 0 1) DegreeOneSmallSpectrum095.graph sourceMap0385=true := by decide +kernel
theorem fusedMap0385_checked : acceptsGraphIso
    (fused (graph core0385) (root 6) 0 1) SmallGeFourSpectrum016.graph fusedMap0385=true := by decide +kernel
theorem certified0385 : Certified (graph core0385) (root 6) 0 1 :=
  of_native_maps core0385 DegreeOneSmallSpectrum095.graph SmallGeFourSpectrum016.graph
    sourceMap0385 fusedMap0385 sourceMap0385_checked fusedMap0385_checked
    DegreeOneSmallComparisons.comparison0385
#print axioms sourceMap0385_checked
#print axioms fusedMap0385_checked
#print axioms certified0385
def sourceMap0385swap : (Vertices 6 ⊕ Fin 2 ⊕ Fin 1) → Fin 10 :=
  fun v => ![6,0,1,2,3,4,5,7,8,9] (sourceLabel 6 1 0 v)
def fusedMap0385swap : (Vertices 6 ⊕ Fin 3) → Fin 10 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9] (fusedLabel 6 1 0 v)
theorem sourceMap0385swap_checked : acceptsGraphIso
    (source (graph core0385) (root 6) 1 0) DegreeOneSmallSpectrum095.graph sourceMap0385swap=true := by decide +kernel
theorem fusedMap0385swap_checked : acceptsGraphIso
    (fused (graph core0385) (root 6) 1 0) SmallGeFourSpectrum016.graph fusedMap0385swap=true := by decide +kernel
theorem certified0385swap : Certified (graph core0385) (root 6) 1 0 :=
  of_native_maps core0385 DegreeOneSmallSpectrum095.graph SmallGeFourSpectrum016.graph
    sourceMap0385swap fusedMap0385swap sourceMap0385swap_checked fusedMap0385swap_checked
    DegreeOneSmallComparisons.comparison0385
#print axioms sourceMap0385swap_checked
#print axioms fusedMap0385swap_checked
#print axioms certified0385swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
