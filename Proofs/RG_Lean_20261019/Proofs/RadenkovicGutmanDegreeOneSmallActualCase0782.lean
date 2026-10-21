/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0782 : Family 8 := level8.get ⟨12,by decide⟩
def sourceMap0782 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,8,9,10,11] (sourceLabel 8 1 1 v)
def fusedMap0782 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 1 1 v)
theorem sourceMap0782_checked : acceptsGraphIso
    (source (graph core0782) (root 8) 1 1) DegreeOneSmallSpectrum1256.graph sourceMap0782=true := by decide +kernel
theorem fusedMap0782_checked : acceptsGraphIso
    (fused (graph core0782) (root 8) 1 1) DegreeOneSmallSpectrum908.graph fusedMap0782=true := by decide +kernel
theorem certified0782 : Certified (graph core0782) (root 8) 1 1 :=
  of_native_maps core0782 DegreeOneSmallSpectrum1256.graph DegreeOneSmallSpectrum908.graph
    sourceMap0782 fusedMap0782 sourceMap0782_checked fusedMap0782_checked
    DegreeOneSmallComparisons.comparison0782
#print axioms sourceMap0782_checked
#print axioms fusedMap0782_checked
#print axioms certified0782
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
