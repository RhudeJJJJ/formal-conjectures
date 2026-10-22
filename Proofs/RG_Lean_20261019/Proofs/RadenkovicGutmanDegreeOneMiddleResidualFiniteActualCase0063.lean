/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons01
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0063 : Family 8 := level8.get ⟨4,by decide⟩
def sourceMap0063 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![2,1,0,9,10,11,12,13,14,3,4,5,6,7,8] (sourceLabel 8 2 2 v)
def fusedMap0063 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap0063_checked : acceptsGraphIso
    (source (graph core0063) (root 8) 2 2) DegreeTwoThreeSpectrum2825.graph sourceMap0063=true := by decide +kernel
theorem fusedMap0063_checked : acceptsGraphIso
    (fused (graph core0063) (root 8) 2 2) DegreeTwoThreeSpectrum2312.graph fusedMap0063=true := by decide +kernel
theorem certified0063 : Certified (graph core0063) (root 8) 2 2 :=
  of_native_maps core0063 DegreeTwoThreeSpectrum2825.graph DegreeTwoThreeSpectrum2312.graph
    sourceMap0063 fusedMap0063 sourceMap0063_checked fusedMap0063_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0063
#print axioms sourceMap0063_checked
#print axioms fusedMap0063_checked
#print axioms certified0063
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
