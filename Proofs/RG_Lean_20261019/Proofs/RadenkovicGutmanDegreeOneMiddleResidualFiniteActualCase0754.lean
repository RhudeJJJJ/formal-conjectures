/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons15
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core0754 : Family 10 := level10.get ⟨394,by decide⟩
def sourceMap0754 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,8,9,10,11,12,13,14,15,16,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap0754 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap0754_checked : acceptsGraphIso
    (source (graph core0754) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1911.graph sourceMap0754=true := by decide +kernel
theorem fusedMap0754_checked : acceptsGraphIso
    (fused (graph core0754) (root 10) 2 2) DegreeTwoThreeSpectrum5741.graph fusedMap0754=true := by decide +kernel
theorem certified0754 : Certified (graph core0754) (root 10) 2 2 :=
  of_native_maps core0754 DegreeOneMiddleResidualSpectrum1911.graph DegreeTwoThreeSpectrum5741.graph
    sourceMap0754 fusedMap0754 sourceMap0754_checked fusedMap0754_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison0754
#print axioms sourceMap0754_checked
#print axioms fusedMap0754_checked
#print axioms certified0754
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
