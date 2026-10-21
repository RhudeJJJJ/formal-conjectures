/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0802 : Family 8 := level8.get ⟨18,by decide⟩
def sourceMap0802 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,7,3,4,5,6] (sourceLabel 8 1 1 v)
def fusedMap0802 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,12,8,9,10,11] (fusedLabel 8 1 1 v)
theorem sourceMap0802_checked : acceptsGraphIso
    (source (graph core0802) (root 8) 1 1) DegreeOneSmallSpectrum1327.graph sourceMap0802=true := by decide +kernel
theorem fusedMap0802_checked : acceptsGraphIso
    (fused (graph core0802) (root 8) 1 1) DegreeOneSmallSpectrum944.graph fusedMap0802=true := by decide +kernel
theorem certified0802 : Certified (graph core0802) (root 8) 1 1 :=
  of_native_maps core0802 DegreeOneSmallSpectrum1327.graph DegreeOneSmallSpectrum944.graph
    sourceMap0802 fusedMap0802 sourceMap0802_checked fusedMap0802_checked
    DegreeOneSmallComparisons.comparison0802
#print axioms sourceMap0802_checked
#print axioms fusedMap0802_checked
#print axioms certified0802
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
