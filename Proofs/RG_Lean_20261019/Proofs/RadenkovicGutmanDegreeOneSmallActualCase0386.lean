/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons07
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0386 : Family 6 := level6.get ⟨19,by decide⟩
def sourceMap0386 : (Vertices 6 ⊕ Fin 1 ⊕ Fin 3) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,10,7,8,9] (sourceLabel 6 0 2 v)
def fusedMap0386 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 0 2 v)
theorem sourceMap0386_checked : acceptsGraphIso
    (source (graph core0386) (root 6) 0 2) DegreeOneSmallSpectrum244.graph sourceMap0386=true := by decide +kernel
theorem fusedMap0386_checked : acceptsGraphIso
    (fused (graph core0386) (root 6) 0 2) SmallGeFourSpectrum037.graph fusedMap0386=true := by decide +kernel
theorem certified0386 : Certified (graph core0386) (root 6) 0 2 :=
  of_native_maps core0386 DegreeOneSmallSpectrum244.graph SmallGeFourSpectrum037.graph
    sourceMap0386 fusedMap0386 sourceMap0386_checked fusedMap0386_checked
    DegreeOneSmallComparisons.comparison0386
#print axioms sourceMap0386_checked
#print axioms fusedMap0386_checked
#print axioms certified0386
def sourceMap0386swap : (Vertices 6 ⊕ Fin 3 ⊕ Fin 1) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (sourceLabel 6 2 0 v)
def fusedMap0386swap : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 2 0 v)
theorem sourceMap0386swap_checked : acceptsGraphIso
    (source (graph core0386) (root 6) 2 0) DegreeOneSmallSpectrum244.graph sourceMap0386swap=true := by decide +kernel
theorem fusedMap0386swap_checked : acceptsGraphIso
    (fused (graph core0386) (root 6) 2 0) SmallGeFourSpectrum037.graph fusedMap0386swap=true := by decide +kernel
theorem certified0386swap : Certified (graph core0386) (root 6) 2 0 :=
  of_native_maps core0386 DegreeOneSmallSpectrum244.graph SmallGeFourSpectrum037.graph
    sourceMap0386swap fusedMap0386swap sourceMap0386swap_checked fusedMap0386swap_checked
    DegreeOneSmallComparisons.comparison0386
#print axioms sourceMap0386swap_checked
#print axioms fusedMap0386swap_checked
#print axioms certified0386swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
