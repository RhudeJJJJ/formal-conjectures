/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0086 : Family 8 := level8.get ⟨35,by decide⟩
def sourceMap0086 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0086 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0086_checked : acceptsGraphIso
    (source (graph core0086) (root 8) 2 2) DegreeOneMiddleResidualSpectrum271.graph sourceMap0086=true := by decide +kernel
theorem fusedMap0086_checked : acceptsGraphIso
    (fused (graph core0086) (root 8) 2 2) DegreeTwoThreeSpectrum2315.graph fusedMap0086=true := by decide +kernel
theorem certified0086 : Certified (graph core0086) (root 8) 2 2 :=
  of_native_maps core0086 DegreeOneMiddleResidualSpectrum271.graph DegreeTwoThreeSpectrum2315.graph
    sourceMap0086 fusedMap0086 sourceMap0086_checked fusedMap0086_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0086
#print axioms sourceMap0086_checked
#print axioms fusedMap0086_checked
#print axioms certified0086
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
