/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons16
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0816 : Family 10 := level10.get ⟨518,by decide⟩
def sourceMap0816 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap0816 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0816_checked : acceptsGraphIso
    (source (graph core0816) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1999.graph sourceMap0816=true := by decide +kernel
theorem fusedMap0816_checked : acceptsGraphIso
    (fused (graph core0816) (root 10) 2 2) DegreeTwoThreeSpectrum5161.graph fusedMap0816=true := by decide +kernel
theorem certified0816 : Certified (graph core0816) (root 10) 2 2 :=
  of_native_maps core0816 DegreeOneMiddleResidualSpectrum1999.graph DegreeTwoThreeSpectrum5161.graph
    sourceMap0816 fusedMap0816 sourceMap0816_checked fusedMap0816_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0816
#print axioms sourceMap0816_checked
#print axioms fusedMap0816_checked
#print axioms certified0816
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
