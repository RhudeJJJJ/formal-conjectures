/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneMiddleResidualFiniteComparisons20
namespace Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1033 : Family 10 := level10.get ⟨1004,by decide⟩
def sourceMap1033 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap1033 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap1033_checked : acceptsGraphIso
    (source (graph core1033) (root 10) 2 2) DegreeOneMiddleResidualSpectrum1966.graph sourceMap1033=true := by decide +kernel
theorem fusedMap1033_checked : acceptsGraphIso
    (fused (graph core1033) (root 10) 2 2) DegreeTwoThreeSpectrum5986.graph fusedMap1033=true := by decide +kernel
theorem certified1033 : Certified (graph core1033) (root 10) 2 2 :=
  of_native_maps core1033 DegreeOneMiddleResidualSpectrum1966.graph DegreeTwoThreeSpectrum5986.graph
    sourceMap1033 fusedMap1033 sourceMap1033_checked fusedMap1033_checked
    DegreeOneMiddleResidualFiniteComparisons.comparison1033
#print axioms sourceMap1033_checked
#print axioms fusedMap1033_checked
#print axioms certified1033
end Gebendorfer.RadenkovicGutman.DegreeOneMiddleResidualFiniteActualCases
