/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons04
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0205 : Family 9 := level9.get ⟨7,by decide⟩
def sourceMap0205 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![2,1,0,10,11,12,13,14,15,9,3,4,5,6,7,8] (sourceLabel 9 2 2 v)
def fusedMap0205 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,2,3,4,5,6,7] (fusedLabel 9 2 2 v)
theorem sourceMap0205_checked : acceptsGraphIso
    (source (graph core0205) (root 9) 2 2) DegreeTwoThreeSpectrum4060.graph sourceMap0205=true := by decide +kernel
theorem fusedMap0205_checked : acceptsGraphIso
    (fused (graph core0205) (root 9) 2 2) DegreeTwoThreeSpectrum3892.graph fusedMap0205=true := by decide +kernel
theorem certified0205 : Certified (graph core0205) (root 9) 2 2 :=
  of_native_maps core0205 DegreeTwoThreeSpectrum4060.graph DegreeTwoThreeSpectrum3892.graph
    sourceMap0205 fusedMap0205 sourceMap0205_checked fusedMap0205_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0205
#print axioms sourceMap0205_checked
#print axioms fusedMap0205_checked
#print axioms certified0205
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
