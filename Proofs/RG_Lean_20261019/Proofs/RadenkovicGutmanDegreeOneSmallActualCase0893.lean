/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0893 : Family 8 := level8.get ⟨53,by decide⟩
def sourceMap0893 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0893 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0893_checked : acceptsGraphIso
    (source (graph core0893) (root 8) 0 2) DegreeOneSmallSpectrum1312.graph sourceMap0893=true := by decide +kernel
theorem fusedMap0893_checked : acceptsGraphIso
    (fused (graph core0893) (root 8) 0 2) DegreeOneSmallSpectrum909.graph fusedMap0893=true := by decide +kernel
theorem certified0893 : Certified (graph core0893) (root 8) 0 2 :=
  of_native_maps core0893 DegreeOneSmallSpectrum1312.graph DegreeOneSmallSpectrum909.graph
    sourceMap0893 fusedMap0893 sourceMap0893_checked fusedMap0893_checked
    DegreeOneSmallComparisons.comparison0893
#print axioms sourceMap0893_checked
#print axioms fusedMap0893_checked
#print axioms certified0893
def sourceMap0893swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0893swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0893swap_checked : acceptsGraphIso
    (source (graph core0893) (root 8) 2 0) DegreeOneSmallSpectrum1312.graph sourceMap0893swap=true := by decide +kernel
theorem fusedMap0893swap_checked : acceptsGraphIso
    (fused (graph core0893) (root 8) 2 0) DegreeOneSmallSpectrum909.graph fusedMap0893swap=true := by decide +kernel
theorem certified0893swap : Certified (graph core0893) (root 8) 2 0 :=
  of_native_maps core0893 DegreeOneSmallSpectrum1312.graph DegreeOneSmallSpectrum909.graph
    sourceMap0893swap fusedMap0893swap sourceMap0893swap_checked fusedMap0893swap_checked
    DegreeOneSmallComparisons.comparison0893
#print axioms sourceMap0893swap_checked
#print axioms fusedMap0893swap_checked
#print axioms certified0893swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
