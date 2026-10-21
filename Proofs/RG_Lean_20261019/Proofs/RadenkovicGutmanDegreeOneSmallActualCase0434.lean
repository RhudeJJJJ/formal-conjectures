/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons08
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0434 : Family 6 := level6.get ⟨29,by decide⟩
def sourceMap0434 : (Vertices 6 ⊕ Fin 2 ⊕ Fin 2) → Fin 11 :=
  fun v => ![0,5,6,7,8,9,10,1,2,3,4] (sourceLabel 6 1 1 v)
def fusedMap0434 : (Vertices 6 ⊕ Fin 4) → Fin 11 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10] (fusedLabel 6 1 1 v)
theorem sourceMap0434_checked : acceptsGraphIso
    (source (graph core0434) (root 6) 1 1) SmallGeFourSpectrum059.graph sourceMap0434=true := by decide +kernel
theorem fusedMap0434_checked : acceptsGraphIso
    (fused (graph core0434) (root 6) 1 1) SmallGeFourSpectrum038.graph fusedMap0434=true := by decide +kernel
theorem certified0434 : Certified (graph core0434) (root 6) 1 1 :=
  of_native_maps core0434 SmallGeFourSpectrum059.graph SmallGeFourSpectrum038.graph
    sourceMap0434 fusedMap0434 sourceMap0434_checked fusedMap0434_checked
    DegreeOneSmallComparisons.comparison0434
#print axioms sourceMap0434_checked
#print axioms fusedMap0434_checked
#print axioms certified0434
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
