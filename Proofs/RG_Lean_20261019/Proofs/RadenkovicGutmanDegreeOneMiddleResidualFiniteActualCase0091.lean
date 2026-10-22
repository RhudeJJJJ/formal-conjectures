/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0091 : Family 8 := level8.get ⟨41,by decide⟩
def sourceMap0091 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (sourceLabel 8 2 2 v)
def fusedMap0091 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0091_checked : acceptsGraphIso
    (source (graph core0091) (root 8) 2 2) DegreeOneMiddleResidualSpectrum287.graph sourceMap0091=true := by decide +kernel
theorem fusedMap0091_checked : acceptsGraphIso
    (fused (graph core0091) (root 8) 2 2) DegreeTwoThreeSpectrum2323.graph fusedMap0091=true := by decide +kernel
theorem certified0091 : Certified (graph core0091) (root 8) 2 2 :=
  of_native_maps core0091 DegreeOneMiddleResidualSpectrum287.graph DegreeTwoThreeSpectrum2323.graph
    sourceMap0091 fusedMap0091 sourceMap0091_checked fusedMap0091_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0091
#print axioms sourceMap0091_checked
#print axioms fusedMap0091_checked
#print axioms certified0091
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
