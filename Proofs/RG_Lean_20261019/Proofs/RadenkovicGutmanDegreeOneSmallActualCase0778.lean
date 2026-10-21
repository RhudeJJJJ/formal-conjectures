/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0778 : Family 8 := level8.get ⟨11,by decide⟩
def sourceMap0778 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,12,8,9,10,11] (sourceLabel 8 1 1 v)
def fusedMap0778 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap0778_checked : acceptsGraphIso
    (source (graph core0778) (root 8) 1 1) DegreeOneSmallSpectrum1257.graph sourceMap0778=true := by decide +kernel
theorem fusedMap0778_checked : acceptsGraphIso
    (fused (graph core0778) (root 8) 1 1) DegreeOneSmallSpectrum894.graph fusedMap0778=true := by decide +kernel
theorem certified0778 : Certified (graph core0778) (root 8) 1 1 :=
  of_native_maps core0778 DegreeOneSmallSpectrum1257.graph DegreeOneSmallSpectrum894.graph
    sourceMap0778 fusedMap0778 sourceMap0778_checked fusedMap0778_checked
    DegreeOneSmallComparisons.comparison0778
#print axioms sourceMap0778_checked
#print axioms fusedMap0778_checked
#print axioms certified0778
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
