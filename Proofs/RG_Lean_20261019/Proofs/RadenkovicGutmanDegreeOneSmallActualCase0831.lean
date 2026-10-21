/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0831 : Family 8 := level8.get ⟨29,by decide⟩
def sourceMap0831 : (Vertices 8 ⊕ Fin 1 ⊕ Fin 1) → Fin 11 :=
  fun v => ![2,1,0,7,8,9,10,5,6,3,4] (sourceLabel 8 0 0 v)
def fusedMap0831 : (Vertices 8 ⊕ Fin 2) → Fin 11 :=
  fun v => ![2,1,0,7,8,9,10,5,6,3,4] (fusedLabel 8 0 0 v)
theorem sourceMap0831_checked : acceptsGraphIso
    (source (graph core0831) (root 8) 0 0) DegreeOneSmallSpectrum176.graph sourceMap0831=true := by decide +kernel
theorem fusedMap0831_checked : acceptsGraphIso
    (fused (graph core0831) (root 8) 0 0) DegreeOneSmallSpectrum222.graph fusedMap0831=true := by decide +kernel
theorem certified0831 : Certified (graph core0831) (root 8) 0 0 :=
  of_native_maps core0831 DegreeOneSmallSpectrum176.graph DegreeOneSmallSpectrum222.graph
    sourceMap0831 fusedMap0831 sourceMap0831_checked fusedMap0831_checked
    DegreeOneSmallComparisons.comparison0831
#print axioms sourceMap0831_checked
#print axioms fusedMap0831_checked
#print axioms certified0831
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
