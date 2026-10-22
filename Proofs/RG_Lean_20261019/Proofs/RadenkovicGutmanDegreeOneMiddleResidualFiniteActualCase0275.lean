/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0275 : Family 9 := level9.get ⟨101,by decide⟩
def sourceMap0275 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,9,10,11,12,13,14,15,8,2,3,4,5,6,7] (sourceLabel 9 2 2 v)
def fusedMap0275 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0275_checked : acceptsGraphIso
    (source (graph core0275) (root 9) 2 2) DegreeOneMiddleResidualSpectrum701.graph sourceMap0275=true := by decide +kernel
theorem fusedMap0275_checked : acceptsGraphIso
    (fused (graph core0275) (root 9) 2 2) DegreeTwoThreeSpectrum4089.graph fusedMap0275=true := by decide +kernel
theorem certified0275 : Certified (graph core0275) (root 9) 2 2 :=
  of_native_maps core0275 DegreeOneMiddleResidualSpectrum701.graph DegreeTwoThreeSpectrum4089.graph
    sourceMap0275 fusedMap0275 sourceMap0275_checked fusedMap0275_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0275
#print axioms sourceMap0275_checked
#print axioms fusedMap0275_checked
#print axioms certified0275
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
