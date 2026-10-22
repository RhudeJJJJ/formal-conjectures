/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0230 : Family 9 := level9.get ⟨38,by decide⟩
def sourceMap0230 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,1,0,11,12,13,14,15,9,10,3,4,5,6,7,8] (sourceLabel 9 2 2 v)
def fusedMap0230 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0230_checked : acceptsGraphIso
    (source (graph core0230) (root 9) 2 2) DegreeTwoThreeSpectrum4559.graph sourceMap0230=true := by decide +kernel
theorem fusedMap0230_checked : acceptsGraphIso
    (fused (graph core0230) (root 9) 2 2) DegreeTwoThreeSpectrum3888.graph fusedMap0230=true := by decide +kernel
theorem certified0230 : Certified (graph core0230) (root 9) 2 2 :=
  of_native_maps core0230 DegreeTwoThreeSpectrum4559.graph DegreeTwoThreeSpectrum3888.graph
    sourceMap0230 fusedMap0230 sourceMap0230_checked fusedMap0230_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0230
#print axioms sourceMap0230_checked
#print axioms fusedMap0230_checked
#print axioms certified0230
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
