/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons05
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0250 : Family 9 := level9.get ⟨65,by decide⟩
def sourceMap0250 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![7,6,0,1,2,3,4,5,14,15,8,9,10,11,12,13] (sourceLabel 9 2 2 v)
def fusedMap0250 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap0250_checked : acceptsGraphIso
    (source (graph core0250) (root 9) 2 2) DegreeOneMiddleResidualSpectrum633.graph sourceMap0250=true := by decide +kernel
theorem fusedMap0250_checked : acceptsGraphIso
    (fused (graph core0250) (root 9) 2 2) DegreeTwoThreeSpectrum3975.graph fusedMap0250=true := by decide +kernel
theorem certified0250 : Certified (graph core0250) (root 9) 2 2 :=
  of_native_maps core0250 DegreeOneMiddleResidualSpectrum633.graph DegreeTwoThreeSpectrum3975.graph
    sourceMap0250 fusedMap0250 sourceMap0250_checked fusedMap0250_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0250
#print axioms sourceMap0250_checked
#print axioms fusedMap0250_checked
#print axioms certified0250
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
