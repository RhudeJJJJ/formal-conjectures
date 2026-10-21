/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons17
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0857 : Family 8 := level8.get ⟨39,by decide⟩
def sourceMap0857 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 3) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,12,9,10,11] (sourceLabel 8 0 2 v)
def fusedMap0857 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 0 2 v)
theorem sourceMap0857_checked : acceptsGraphIso
    (source (graph core0857) (root 8) 0 2) DegreeOneSmallSpectrum1111.graph sourceMap0857=true := by decide +kernel
theorem fusedMap0857_checked : acceptsGraphIso
    (fused (graph core0857) (root 8) 0 2) DegreeOneSmallSpectrum871.graph fusedMap0857=true := by decide +kernel
theorem certified0857 : Certified (graph core0857) (root 8) 0 2 :=
  of_native_maps core0857 DegreeOneSmallSpectrum1111.graph DegreeOneSmallSpectrum871.graph
    sourceMap0857 fusedMap0857 sourceMap0857_checked fusedMap0857_checked
    DegreeOneSmallComparisons.comparison0857
#print axioms sourceMap0857_checked
#print axioms fusedMap0857_checked
#print axioms certified0857
def sourceMap0857swap : (Vertices 8 ⊕ Fin 3 ⊕ Fin 1) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 2 0 v)
def fusedMap0857swap : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 2 0 v)
theorem sourceMap0857swap_checked : acceptsGraphIso
    (source (graph core0857) (root 8) 2 0) DegreeOneSmallSpectrum1111.graph sourceMap0857swap=true := by decide +kernel
theorem fusedMap0857swap_checked : acceptsGraphIso
    (fused (graph core0857) (root 8) 2 0) DegreeOneSmallSpectrum871.graph fusedMap0857swap=true := by decide +kernel
theorem certified0857swap : Certified (graph core0857) (root 8) 2 0 :=
  of_native_maps core0857 DegreeOneSmallSpectrum1111.graph DegreeOneSmallSpectrum871.graph
    sourceMap0857swap fusedMap0857swap sourceMap0857swap_checked fusedMap0857swap_checked
    DegreeOneSmallComparisons.comparison0857
#print axioms sourceMap0857swap_checked
#print axioms fusedMap0857swap_checked
#print axioms certified0857swap
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
