/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0231 : Family 9 := level9.get ⟨39,by decide⟩
def sourceMap0231 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,1,0,11,12,13,14,15,9,10,3,4,5,6,7,8] (sourceLabel 9 2 2 v)
def fusedMap0231 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0231_checked : acceptsGraphIso
    (source (graph core0231) (root 9) 2 2) DegreeTwoThreeSpectrum4560.graph sourceMap0231=true := by decide +kernel
theorem fusedMap0231_checked : acceptsGraphIso
    (fused (graph core0231) (root 9) 2 2) DegreeTwoThreeSpectrum3889.graph fusedMap0231=true := by decide +kernel
theorem certified0231 : Certified (graph core0231) (root 9) 2 2 :=
  of_native_maps core0231 DegreeTwoThreeSpectrum4560.graph DegreeTwoThreeSpectrum3889.graph
    sourceMap0231 fusedMap0231 sourceMap0231_checked fusedMap0231_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0231
#print axioms sourceMap0231_checked
#print axioms fusedMap0231_checked
#print axioms certified0231
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
